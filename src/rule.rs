use crate::context::{Context, IStr};
use indexmap::{indexset, IndexMap, IndexSet};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::Hash;
use std::iter;
use std::ops::{Add, BitAnd, BitOr};
use std::rc::Rc;

#[derive(Clone)]
pub struct RuleWithNamedFields<Pat> {
    pub rule: Rc<Rule<Pat>>,
    pub fields: IndexMap<IStr, FieldPathset>,
}

#[derive(Clone, Default)]
pub struct FieldPathset(pub IndexSet<Vec<usize>>);

impl FieldPathset {
    fn prepend_all(self, i: usize) -> Self {
        FieldPathset(
            self.0
                .into_iter()
                .map(|mut path| {
                    path.insert(0, i);
                    path
                })
                .collect(),
        )
    }
}

/// Helpers for building rules without needing a `Context` until the very end.
///
/// NOTE: the module is private to disallow referring to the trait / types,
/// as they are an implementation detail of the builder methods and operators.
mod build {
    use super::*;

    // HACK(eddyb) like `Into<Self::Out>` but using an associated type.
    // Needed for constraining the RHS of operator overload impls.
    pub trait Start {
        type Out;

        fn start(self) -> Self::Out;
    }

    impl<Pat> Start for RuleWithNamedFields<Pat> {
        type Out = RuleWithNamedFields<Pat>;

        fn start(self) -> Self::Out {
            self
        }
    }

    pub trait Finish<Pat> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat>;
    }

    impl<Pat> Finish<Pat> for RuleWithNamedFields<Pat> {
        fn finish(self, _cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat> {
            self
        }
    }

    pub struct Empty;

    impl<Pat> Finish<Pat> for Empty {
        fn finish(self, _cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat> {
            RuleWithNamedFields {
                rule: Rc::new(Rule::Empty),
                fields: IndexMap::new(),
            }
        }
    }

    pub struct Eat<Pat>(Pat);

    impl<Pat> Finish<Pat> for Eat<Pat> {
        fn finish(self, _cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat> {
            RuleWithNamedFields {
                rule: Rc::new(Rule::Eat(self.0)),
                fields: IndexMap::new(),
            }
        }
    }

    pub struct Call<'a>(&'a str);

    impl<Pat> Finish<Pat> for Call<'_> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat> {
            RuleWithNamedFields {
                rule: Rc::new(Rule::Call(cx.intern(self.0))),
                fields: IndexMap::new(),
            }
        }
    }

    pub struct Field<'a, R>(R, &'a str);

    impl<Pat, R: Finish<Pat>> Finish<Pat> for Field<'_, R> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat> {
            let mut rule = self.0.finish(cx);
            let name = cx.intern(self.1);
            let path = match &*rule.rule {
                Rule::RepeatMany(rule, _) | Rule::RepeatMore(rule, _) => match **rule {
                    Rule::Eat(_) | Rule::Call(_) => vec![],
                    _ => unimplemented!(),
                },
                Rule::Opt(_) => vec![0],
                _ => vec![],
            };
            rule.fields.insert(name, FieldPathset(indexset![path]));
            rule
        }
    }

    pub struct Opt<R>(R);

    impl<Pat, R: Finish<Pat>> Finish<Pat> for Opt<R> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat> {
            let rule = self.0.finish(cx);
            RuleWithNamedFields {
                rule: Rc::new(Rule::Opt(rule.rule)),
                fields: rule
                    .fields
                    .into_iter()
                    .map(|(name, paths)| (name, paths.prepend_all(0)))
                    .collect(),
            }
        }
    }

    pub struct RepeatMany<E>(E);

    impl<Pat, E: Finish<Pat>> Finish<Pat> for RepeatMany<E> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat> {
            let elem = self.0.finish(cx);
            RuleWithNamedFields {
                rule: Rc::new(Rule::RepeatMany(elem.rule, None)),
                fields: elem
                    .fields
                    .into_iter()
                    .map(|(name, paths)| (name, paths.prepend_all(0)))
                    .collect(),
            }
        }
    }

    pub struct RepeatManySep<E, S>(E, S, SepKind);

    impl<Pat, E: Finish<Pat>, S: Finish<Pat>> Finish<Pat> for RepeatManySep<E, S> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat> {
            let elem = self.0.finish(cx);
            let sep = self.1.finish(cx);
            assert!(sep.fields.is_empty());
            RuleWithNamedFields {
                rule: Rc::new(Rule::RepeatMany(elem.rule, Some((sep.rule, self.2)))),
                fields: elem
                    .fields
                    .into_iter()
                    .map(|(name, paths)| (name, paths.prepend_all(0)))
                    .collect(),
            }
        }
    }

    pub struct RepeatMore<E>(E);

    impl<Pat, E: Finish<Pat>> Finish<Pat> for RepeatMore<E> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat> {
            let elem = self.0.finish(cx);
            RuleWithNamedFields {
                rule: Rc::new(Rule::RepeatMore(elem.rule, None)),
                fields: elem
                    .fields
                    .into_iter()
                    .map(|(name, paths)| (name, paths.prepend_all(0)))
                    .collect(),
            }
        }
    }

    pub struct RepeatMoreSep<E, S>(E, S, SepKind);

    impl<Pat, E: Finish<Pat>, S: Finish<Pat>> Finish<Pat> for RepeatMoreSep<E, S> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat> {
            let elem = self.0.finish(cx);
            let sep = self.1.finish(cx);
            assert!(sep.fields.is_empty());
            RuleWithNamedFields {
                rule: Rc::new(Rule::RepeatMore(elem.rule, Some((sep.rule, self.2)))),
                fields: elem
                    .fields
                    .into_iter()
                    .map(|(name, paths)| (name, paths.prepend_all(0)))
                    .collect(),
            }
        }
    }

    pub struct Concat<A, B>(A, B);

    impl<Pat, A: Finish<Pat>, B: Finish<Pat>> Finish<Pat> for Concat<A, B> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat> {
            let a = self.0.finish(cx);
            let b = self.1.finish(cx);

            match (&*a.rule, &*b.rule) {
                (Rule::Empty, _) if a.fields.is_empty() => return b,
                (_, Rule::Empty) if b.fields.is_empty() => return a,
                _ => {}
            }

            let mut fields: IndexMap<_, _> = a
                .fields
                .into_iter()
                .map(|(name, paths)| (name, paths.prepend_all(0)))
                .collect();
            for (name, paths) in b.fields {
                assert!(!fields.contains_key(&name), "duplicate field {}", cx[name]);
                fields.insert(name, paths.prepend_all(1));
            }
            RuleWithNamedFields {
                rule: Rc::new(Rule::Concat([a.rule, b.rule])),
                fields,
            }
        }
    }

    pub struct Or<A, B>(A, B);

    impl<Pat, A: Finish<Pat>, B: Finish<Pat>> Finish<Pat> for Or<A, B> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat> {
            let a = self.0.finish(cx);
            let b = self.1.finish(cx);

            let (old_rules, a, mut fields) = match &*a.rule {
                Rule::Or(rules) => (&rules[..], None, a.fields),
                _ => (&[][..], Some(a), IndexMap::new()),
            };

            let new_rules = a
                .into_iter()
                .chain(iter::once(b))
                .enumerate()
                .map(|(i, rule)| {
                    for (name, paths) in rule.fields {
                        fields
                            .entry(name)
                            .or_default()
                            .0
                            .extend(paths.prepend_all(old_rules.len() + i).0);
                    }

                    rule.rule
                });
            let rules = old_rules.iter().cloned().chain(new_rules).collect();

            RuleWithNamedFields {
                rule: Rc::new(Rule::Or(rules)),
                fields,
            }
        }
    }

    /// Wrapper for building rules, to allow overloading operators uniformly.
    pub struct Build<R>(R);

    impl<R> Start for Build<R> {
        type Out = R;

        fn start(self) -> R {
            self.0
        }
    }

    impl<R> Build<R> {
        pub fn finish<Pat>(self, cx: &mut Context<Pat>) -> RuleWithNamedFields<Pat>
        where
            R: Finish<Pat>,
        {
            Finish::finish(self.0, cx)
        }
    }

    pub fn empty() -> build::Build<build::Empty> {
        build::Build(build::Empty)
    }

    pub fn eat<Pat>(pat: impl Into<Pat>) -> build::Build<build::Eat<Pat>> {
        build::Build(build::Eat(pat.into()))
    }

    pub fn call(name: &str) -> build::Build<build::Call<'_>> {
        build::Build(build::Call(name))
    }

    /// Helper macro to provide methods and operator overloads on both
    /// `RuleWithNamedFields` and `Build<R>`, instead of just one of them.
    macro_rules! builder_impls {
        (impl<$($g:ident),*> $Self:ty) => {
            impl<$($g),*> $Self {
                pub fn field<'a>(self, name: &'a str) -> Build<Field<'a, <Self as Start>::Out>> {
                    Build(Field(self.start(), name))
                }

                pub fn opt(self) -> Build<Opt<<Self as Start>::Out>> {
                    Build(Opt(self.start()))
                }

                pub fn repeat_many(self) -> Build<RepeatMany<<Self as Start>::Out>> {
                    Build(RepeatMany(self.start()))
                }

                pub fn repeat_many_sep<S: Start>(
                    self,
                    sep: S,
                    kind: SepKind,
                ) -> Build<RepeatManySep<<Self as Start>::Out, S::Out>> {
                    Build(RepeatManySep(self.start(), sep.start(), kind))
                }

                pub fn repeat_more(self) -> Build<RepeatMore<<Self as Start>::Out>> {
                    Build(RepeatMore(self.start()))
                }

                pub fn repeat_more_sep<S: Start>(
                    self,
                    sep: S,
                    kind: SepKind,
                ) -> Build<RepeatMoreSep<<Self as Start>::Out, S::Out>> {
                    Build(RepeatMoreSep(self.start(), sep.start(), kind))
                }
            }

            impl<$($g,)* Other: Start> Add<Other> for $Self {
                type Output = Build<Concat<<Self as Start>::Out, Other::Out>>;

                fn add(self, other: Other) -> Self::Output {
                    Build(Concat(self.start(), other.start()))
                }
            }

            impl<$($g,)* Other: Start> BitOr<Other> for $Self {
                type Output = Build<Or<<Self as Start>::Out, Other::Out>>;

                fn bitor(self, other: Other) -> Self::Output {
                    Build(Or(self.start(), other.start()))
                }
            }
        };
    }

    builder_impls!(impl<R> Build<R>);
    builder_impls!(impl<Pat> RuleWithNamedFields<Pat>);
}

pub use self::build::{call, eat, empty};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SepKind {
    Simple,
    Trailing,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Rule<Pat> {
    Empty,
    Eat(Pat),
    Call(IStr),

    Concat([Rc<Rule<Pat>>; 2]),
    Or(Vec<Rc<Rule<Pat>>>),

    Opt(Rc<Rule<Pat>>),
    RepeatMany(Rc<Rule<Pat>>, Option<(Rc<Rule<Pat>>, SepKind)>),
    RepeatMore(Rc<Rule<Pat>>, Option<(Rc<Rule<Pat>>, SepKind)>),
}

impl<Pat> Rule<Pat> {
    pub fn field_pathset_is_refutable(&self, paths: &FieldPathset) -> bool {
        if paths.0.len() > 1 {
            true
        } else {
            self.field_is_refutable(paths.0.get_index(0).unwrap())
        }
    }
    pub fn field_is_refutable(&self, path: &[usize]) -> bool {
        match self {
            Rule::Empty
            | Rule::Eat(_)
            | Rule::Call(_)
            | Rule::RepeatMany(..)
            | Rule::RepeatMore(..) => false,
            Rule::Concat(rules) => rules[path[0]].field_is_refutable(&path[1..]),
            Rule::Or(..) | Rule::Opt(_) => true,
        }
    }
}

// FIXME(eddyb) this should just work with `self: &Rc<Self>` on inherent methods,
// but that still requires `#![feature(arbitrary_self_types)]`.
trait RcRuleMethods<Pat>: Sized {
    fn can_be_empty(
        &self,
        cache: &mut HashMap<Self, MaybeKnown<bool>>,
        grammar: &crate::Grammar<Pat>,
    ) -> MaybeKnown<bool>;
}

impl<Pat: Ord + Hash + MatchesEmpty> RcRuleMethods<Pat> for Rc<Rule<Pat>> {
    fn can_be_empty(
        &self,
        cache: &mut HashMap<Self, MaybeKnown<bool>>,
        grammar: &crate::Grammar<Pat>,
    ) -> MaybeKnown<bool> {
        match cache.entry(self.clone()) {
            Entry::Occupied(entry) => return *entry.get(),
            Entry::Vacant(entry) => {
                entry.insert(MaybeKnown::Unknown);
            }
        };
        let r = self.can_be_empty_uncached(cache, grammar);
        match r {
            MaybeKnown::Known(_) => *cache.get_mut(self).unwrap() = r,
            MaybeKnown::Unknown => {
                cache.remove(self);
            }
        }
        r
    }
}

impl<Pat: Ord + Hash + MatchesEmpty> Rule<Pat> {
    fn can_be_empty_uncached(
        &self,
        cache: &mut HashMap<Rc<Self>, MaybeKnown<bool>>,
        grammar: &crate::Grammar<Pat>,
    ) -> MaybeKnown<bool> {
        match self {
            Rule::Empty | Rule::Opt(_) | Rule::RepeatMany(..) => MaybeKnown::Known(true),
            Rule::Eat(pat) => pat.matches_empty(),
            Rule::Call(rule) => grammar.rules[rule].rule.can_be_empty(cache, grammar),
            Rule::Concat([left, right]) => {
                left.can_be_empty(cache, grammar) & right.can_be_empty(cache, grammar)
            }
            Rule::Or(rules) => rules.iter().fold(MaybeKnown::Known(false), |prev, rule| {
                prev | rule.can_be_empty(cache, grammar)
            }),
            Rule::RepeatMore(elem, _) => elem.can_be_empty(cache, grammar),
        }
    }

    pub(crate) fn check_non_empty_opt(
        &self,
        cache: &mut HashMap<Rc<Self>, MaybeKnown<bool>>,
        grammar: &crate::Grammar<Pat>,
    ) {
        match self {
            Rule::Empty | Rule::Eat(_) | Rule::Call(_) => {}
            Rule::Concat([left, right]) => {
                left.check_non_empty_opt(cache, grammar);
                right.check_non_empty_opt(cache, grammar);
            }
            Rule::Or(rules) => {
                for rule in rules {
                    rule.check_non_empty_opt(cache, grammar);
                }
            }
            Rule::Opt(rule) => {
                assert_eq!(rule.can_be_empty(cache, grammar), MaybeKnown::Known(false));
                rule.check_non_empty_opt(cache, grammar)
            }
            Rule::RepeatMany(elem, sep) | Rule::RepeatMore(elem, sep) => {
                assert_eq!(elem.can_be_empty(cache, grammar), MaybeKnown::Known(false));
                elem.check_non_empty_opt(cache, grammar);
                if let Some((sep, _)) = sep {
                    sep.check_non_empty_opt(cache, grammar);
                }
            }
        }
    }

    pub(crate) fn check_call_names(&self, cx: &Context<Pat>, grammar: &crate::Grammar<Pat>) {
        match self {
            Rule::Empty | Rule::Eat(_) => {}
            Rule::Call(rule) => {
                assert!(
                    grammar.rules.contains_key(rule),
                    "no rule named `{}`",
                    cx[*rule]
                );
            }
            Rule::Concat([left, right]) => {
                left.check_call_names(cx, grammar);
                right.check_call_names(cx, grammar);
            }
            Rule::Or(rules) => {
                for rule in rules {
                    rule.check_call_names(cx, grammar);
                }
            }
            Rule::Opt(rule) => rule.check_call_names(cx, grammar),
            Rule::RepeatMany(elem, sep) | Rule::RepeatMore(elem, sep) => {
                elem.check_call_names(cx, grammar);
                if let Some((sep, _)) = sep {
                    sep.check_call_names(cx, grammar);
                }
            }
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MaybeKnown<T> {
    Known(T),
    Unknown,
}

impl BitOr for MaybeKnown<bool> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        match (self, rhs) {
            (MaybeKnown::Known(true), _) | (_, MaybeKnown::Known(true)) => MaybeKnown::Known(true),
            (MaybeKnown::Known(false), x) | (x, MaybeKnown::Known(false)) => x,
            (MaybeKnown::Unknown, MaybeKnown::Unknown) => MaybeKnown::Unknown,
        }
    }
}

impl BitAnd for MaybeKnown<bool> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self {
        match (self, rhs) {
            (MaybeKnown::Known(false), _) | (_, MaybeKnown::Known(false)) => {
                MaybeKnown::Known(false)
            }
            (MaybeKnown::Known(true), x) | (x, MaybeKnown::Known(true)) => x,
            (MaybeKnown::Unknown, MaybeKnown::Unknown) => MaybeKnown::Unknown,
        }
    }
}

pub trait MatchesEmpty {
    fn matches_empty(&self) -> MaybeKnown<bool>;
}

pub trait Folder<Pat>: Sized {
    fn cx(&mut self) -> &mut Context<Pat>;
    fn fold_leaf(&mut self, rule: RuleWithNamedFields<Pat>) -> RuleWithNamedFields<Pat> {
        rule
    }
    fn fold_concat(
        &mut self,
        left: RuleWithNamedFields<Pat>,
        right: RuleWithNamedFields<Pat>,
    ) -> RuleWithNamedFields<Pat> {
        (left.fold(self) + right.fold(self)).finish(self.cx())
    }
    fn fold_or(
        &mut self,
        mut rules: impl Iterator<Item = RuleWithNamedFields<Pat>>,
    ) -> RuleWithNamedFields<Pat> {
        let first = rules.next().unwrap().fold(self);
        rules.fold(first, |or, rule| (or | rule.fold(self)).finish(self.cx()))
    }
    fn fold_opt(&mut self, rule: RuleWithNamedFields<Pat>) -> RuleWithNamedFields<Pat> {
        rule.fold(self).opt().finish(self.cx())
    }
    fn fold_repeat_many(
        &mut self,
        elem: RuleWithNamedFields<Pat>,
        sep: Option<(RuleWithNamedFields<Pat>, SepKind)>,
    ) -> RuleWithNamedFields<Pat> {
        let elem = elem.fold(self);
        let sep = sep.map(|(sep, kind)| (sep.fold(self), kind));
        match sep {
            None => elem.repeat_many().finish(self.cx()),
            Some((sep, kind)) => elem.repeat_many_sep(sep, kind).finish(self.cx()),
        }
    }
    fn fold_repeat_more(
        &mut self,
        elem: RuleWithNamedFields<Pat>,
        sep: Option<(RuleWithNamedFields<Pat>, SepKind)>,
    ) -> RuleWithNamedFields<Pat> {
        let elem = elem.fold(self);
        let sep = sep.map(|(sep, kind)| (sep.fold(self), kind));
        match sep {
            None => elem.repeat_more().finish(self.cx()),
            Some((sep, kind)) => elem.repeat_more_sep(sep, kind).finish(self.cx()),
        }
    }
}

impl<Pat> RuleWithNamedFields<Pat> {
    // HACK(eddyb) this is pretty expensive, find a better way
    fn filter_fields<'a>(
        &'a self,
        field: Option<usize>,
    ) -> impl Iterator<Item = (IStr, FieldPathset)> + 'a {
        self.fields.iter().filter_map(move |(&name, paths)| {
            let paths: IndexSet<_> = paths
                .0
                .iter()
                .filter_map(move |path| {
                    if path.first().cloned() == field {
                        Some(path.get(1..).unwrap_or(&[]).to_vec())
                    } else {
                        None
                    }
                })
                .collect();
            if !paths.is_empty() {
                Some((name, FieldPathset(paths)))
            } else {
                None
            }
        })
    }

    pub fn fold(self, folder: &mut impl Folder<Pat>) -> Self {
        let field_rule = |rule: &Rc<Rule<Pat>>, i| RuleWithNamedFields {
            rule: rule.clone(),
            fields: self.filter_fields(Some(i)).collect(),
        };
        let mut rule = match &*self.rule {
            Rule::Empty | Rule::Eat(_) | Rule::Call(_) => return folder.fold_leaf(self),
            Rule::Concat([left, right]) => {
                folder.fold_concat(field_rule(left, 0), field_rule(right, 1))
            }
            Rule::Or(rules) => folder.fold_or(
                rules
                    .iter()
                    .enumerate()
                    .map(|(i, rule)| field_rule(rule, i)),
            ),
            Rule::Opt(rule) => folder.fold_opt(field_rule(rule, 0)),
            Rule::RepeatMany(elem, sep) => folder.fold_repeat_many(
                field_rule(elem, 0),
                sep.as_ref().map(|(sep, kind)| (field_rule(sep, 1), *kind)),
            ),
            Rule::RepeatMore(elem, sep) => folder.fold_repeat_more(
                field_rule(elem, 0),
                sep.as_ref().map(|(sep, kind)| (field_rule(sep, 1), *kind)),
            ),
        };
        rule.fields.extend(self.filter_fields(None));
        rule
    }

    pub fn insert_whitespace(
        self,
        cx: &mut Context<Pat>,
        whitespace: RuleWithNamedFields<Pat>,
    ) -> Self
    where
        Pat: Clone,
    {
        assert!(whitespace.fields.is_empty());

        struct WhitespaceInserter<'a, Pat> {
            cx: &'a mut Context<Pat>,
            whitespace: RuleWithNamedFields<Pat>,
        }

        impl<Pat: Clone> Folder<Pat> for WhitespaceInserter<'_, Pat> {
            fn cx(&mut self) -> &mut Context<Pat> {
                self.cx
            }
            // FIXME(eddyb) this will insert too many whitespace rules,
            // e.g. `A B? C` becomes `A WS B? WS C`, which when `B` is
            // missing, is `A WS WS C`. Even worse, `A? B` ends up as
            // `A? WS B`, which has an incorrect leading whitespace.
            fn fold_concat(
                &mut self,
                left: RuleWithNamedFields<Pat>,
                right: RuleWithNamedFields<Pat>,
            ) -> RuleWithNamedFields<Pat> {
                (left.fold(self) + self.whitespace.clone() + right.fold(self)).finish(self.cx())
            }
            fn fold_repeat_many(
                &mut self,
                elem: RuleWithNamedFields<Pat>,
                sep: Option<(RuleWithNamedFields<Pat>, SepKind)>,
            ) -> RuleWithNamedFields<Pat> {
                let elem = elem.fold(self);
                let sep = sep.map(|(sep, kind)| (sep.fold(self), kind));
                match sep {
                    // A* => A* % WS
                    None => elem
                        .repeat_more_sep(self.whitespace.clone(), SepKind::Simple)
                        .finish(self.cx),
                    // A* % B => A* % (WS B WS)
                    Some((sep, SepKind::Simple)) => elem
                        .repeat_more_sep(
                            self.whitespace.clone() + sep + self.whitespace.clone(),
                            SepKind::Simple,
                        )
                        .finish(self.cx),
                    // FIXME(cad97) this will insert too many whitespace rules
                    // A* %% B => ???
                    // Currently, A* %% (WS B WS), which allows trailing whitespace incorrectly
                    Some((sep, SepKind::Trailing)) => elem
                        .repeat_more_sep(
                            self.whitespace.clone() + sep + self.whitespace.clone(),
                            SepKind::Trailing,
                        )
                        .finish(self.cx),
                }
            }
            fn fold_repeat_more(
                &mut self,
                elem: RuleWithNamedFields<Pat>,
                sep: Option<(RuleWithNamedFields<Pat>, SepKind)>,
            ) -> RuleWithNamedFields<Pat> {
                let elem = elem.fold(self);
                let sep = sep.map(|(sep, kind)| (sep.fold(self), kind));
                match sep {
                    // A+ => A+ % WS
                    None => elem
                        .repeat_more_sep(self.whitespace.clone(), SepKind::Simple)
                        .finish(self.cx),
                    // A+ % B => A+ % (WS B WS)
                    Some((sep, SepKind::Simple)) => elem
                        .fold(self)
                        .repeat_more_sep(
                            self.whitespace.clone() + sep + self.whitespace.clone(),
                            SepKind::Simple,
                        )
                        .finish(self.cx),
                    // A+ %% B => A+ % (WS B WS) (WS B)?
                    Some((sep, SepKind::Trailing)) => (elem.repeat_more_sep(
                        self.whitespace.clone() + sep.clone() + self.whitespace.clone(),
                        SepKind::Simple,
                    ) + (self.whitespace.clone() + sep).opt())
                    .finish(self.cx),
                }
            }
        }

        self.fold(&mut WhitespaceInserter { cx, whitespace })
    }
}
