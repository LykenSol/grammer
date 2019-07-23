use crate::context::{Context, IRule, IStr};
use indexmap::{indexmap, IndexMap};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::Hash;
use std::iter;
use std::ops::{Add, BitAnd, BitOr};

#[derive(Clone)]
pub struct RuleWithNamedFields {
    pub rule: IRule,
    pub fields: Fields,
}

pub type Fields = IndexMap<IStr, Field>;

#[derive(Clone, Default)]
pub struct Field {
    pub paths: IndexMap<Vec<usize>, Fields>,
}

impl Field {
    fn prepend_paths(self, i: usize) -> Self {
        Field {
            paths: self
                .paths
                .into_iter()
                .map(|(mut path, subfields)| {
                    path.insert(0, i);
                    (path, subfields)
                })
                .collect(),
        }
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

    impl Start for RuleWithNamedFields {
        type Out = RuleWithNamedFields;

        fn start(self) -> Self::Out {
            self
        }
    }

    pub trait Finish<Pat> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields;
    }

    impl<Pat> Finish<Pat> for RuleWithNamedFields {
        fn finish(self, _cx: &mut Context<Pat>) -> RuleWithNamedFields {
            self
        }
    }

    pub struct Empty;

    impl<Pat: Eq + Hash> Finish<Pat> for Empty {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields {
            RuleWithNamedFields {
                rule: cx.intern(Rule::Empty),
                fields: IndexMap::new(),
            }
        }
    }

    pub struct Eat<Pat>(Pat);

    impl<Pat: Eq + Hash> Finish<Pat> for Eat<Pat> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields {
            RuleWithNamedFields {
                rule: cx.intern(Rule::Eat(self.0)),
                fields: IndexMap::new(),
            }
        }
    }

    pub struct Call<'a>(&'a str);

    impl<Pat: Eq + Hash> Finish<Pat> for Call<'_> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields {
            let name = cx.intern(self.0);
            RuleWithNamedFields {
                rule: cx.intern(Rule::Call(name)),
                fields: IndexMap::new(),
            }
        }
    }

    pub struct Field<'a, R>(R, &'a str);

    impl<Pat: Eq + Hash, R: Finish<Pat>> Finish<Pat> for Field<'_, R> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields {
            let mut rule = self.0.finish(cx);
            let name = cx.intern(self.1);
            let path = match cx[rule.rule] {
                Rule::RepeatMany(rule, _) | Rule::RepeatMore(rule, _) => match cx[rule] {
                    Rule::Eat(_) | Rule::Call(_) => vec![],
                    _ => unimplemented!(),
                },
                Rule::Opt(_) => vec![0],
                _ => vec![],
            };
            rule.fields = indexmap! {
                name => super::Field {
                    paths: indexmap! { path => rule.fields },
                },
            };
            rule
        }
    }

    pub struct Opt<R>(R);

    impl<Pat: Eq + Hash, R: Finish<Pat>> Finish<Pat> for Opt<R> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields {
            let rule = self.0.finish(cx);
            RuleWithNamedFields {
                rule: cx.intern(Rule::Opt(rule.rule)),
                fields: rule
                    .fields
                    .into_iter()
                    .map(|(name, field)| (name, field.prepend_paths(0)))
                    .collect(),
            }
        }
    }

    pub struct RepeatMany<E>(E);

    impl<Pat: Eq + Hash, E: Finish<Pat>> Finish<Pat> for RepeatMany<E> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields {
            let elem = self.0.finish(cx);
            RuleWithNamedFields {
                rule: cx.intern(Rule::RepeatMany(elem.rule, None)),
                fields: elem
                    .fields
                    .into_iter()
                    .map(|(name, field)| (name, field.prepend_paths(0)))
                    .collect(),
            }
        }
    }

    pub struct RepeatManySep<E, S>(E, S, SepKind);

    impl<Pat: Eq + Hash, E: Finish<Pat>, S: Finish<Pat>> Finish<Pat> for RepeatManySep<E, S> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields {
            let elem = self.0.finish(cx);
            let sep = self.1.finish(cx);
            assert!(sep.fields.is_empty());
            RuleWithNamedFields {
                rule: cx.intern(Rule::RepeatMany(elem.rule, Some((sep.rule, self.2)))),
                fields: elem
                    .fields
                    .into_iter()
                    .map(|(name, field)| (name, field.prepend_paths(0)))
                    .collect(),
            }
        }
    }

    pub struct RepeatMore<E>(E);

    impl<Pat: Eq + Hash, E: Finish<Pat>> Finish<Pat> for RepeatMore<E> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields {
            let elem = self.0.finish(cx);
            RuleWithNamedFields {
                rule: cx.intern(Rule::RepeatMore(elem.rule, None)),
                fields: elem
                    .fields
                    .into_iter()
                    .map(|(name, field)| (name, field.prepend_paths(0)))
                    .collect(),
            }
        }
    }

    pub struct RepeatMoreSep<E, S>(E, S, SepKind);

    impl<Pat: Eq + Hash, E: Finish<Pat>, S: Finish<Pat>> Finish<Pat> for RepeatMoreSep<E, S> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields {
            let elem = self.0.finish(cx);
            let sep = self.1.finish(cx);
            assert!(sep.fields.is_empty());
            RuleWithNamedFields {
                rule: cx.intern(Rule::RepeatMore(elem.rule, Some((sep.rule, self.2)))),
                fields: elem
                    .fields
                    .into_iter()
                    .map(|(name, field)| (name, field.prepend_paths(0)))
                    .collect(),
            }
        }
    }

    pub struct Concat<A, B>(A, B);

    impl<Pat: Eq + Hash, A: Finish<Pat>, B: Finish<Pat>> Finish<Pat> for Concat<A, B> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields {
            let a = self.0.finish(cx);
            let b = self.1.finish(cx);

            match (&cx[a.rule], &cx[b.rule]) {
                (Rule::Empty, _) if a.fields.is_empty() => return b,
                (_, Rule::Empty) if b.fields.is_empty() => return a,
                _ => {}
            }

            let mut fields: IndexMap<_, _> = a
                .fields
                .into_iter()
                .map(|(name, field)| (name, field.prepend_paths(0)))
                .collect();
            for (name, field) in b.fields {
                assert!(!fields.contains_key(&name), "duplicate field {}", cx[name]);
                fields.insert(name, field.prepend_paths(1));
            }
            RuleWithNamedFields {
                rule: cx.intern(Rule::Concat([a.rule, b.rule])),
                fields,
            }
        }
    }

    pub struct Or<A, B>(A, B);

    impl<Pat: Eq + Hash, A: Finish<Pat>, B: Finish<Pat>> Finish<Pat> for Or<A, B> {
        fn finish(self, cx: &mut Context<Pat>) -> RuleWithNamedFields {
            let a = self.0.finish(cx);
            let b = self.1.finish(cx);

            let (old_rules, a, mut fields) = match cx[a.rule] {
                Rule::Or(ref rules) => (&rules[..], None, a.fields),
                _ => (&[][..], Some(a), IndexMap::new()),
            };

            let new_rules = a
                .into_iter()
                .chain(iter::once(b))
                .enumerate()
                .map(|(i, rule)| {
                    for (name, field) in rule.fields {
                        fields
                            .entry(name)
                            .or_default()
                            .paths
                            .extend(field.prepend_paths(old_rules.len() + i).paths);
                    }

                    rule.rule
                });
            let rules = old_rules.iter().cloned().chain(new_rules).collect();

            RuleWithNamedFields {
                rule: cx.intern(Rule::Or(rules)),
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
        pub fn finish<Pat>(self, cx: &mut Context<Pat>) -> RuleWithNamedFields
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
    builder_impls!(impl<> RuleWithNamedFields);
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

    Concat([IRule; 2]),
    Or(Vec<IRule>),

    Opt(IRule),
    RepeatMany(IRule, Option<(IRule, SepKind)>),
    RepeatMore(IRule, Option<(IRule, SepKind)>),
}

impl IRule {
    pub fn field_is_refutable<Pat>(self, cx: &Context<Pat>, field: &Field) -> bool {
        if field.paths.len() > 1 {
            true
        } else {
            self.field_path_is_refutable(cx, field.paths.get_index(0).unwrap().0)
        }
    }

    pub fn field_path_is_refutable<Pat>(self, cx: &Context<Pat>, path: &[usize]) -> bool {
        match cx[self] {
            Rule::Empty
            | Rule::Eat(_)
            | Rule::Call(_)
            | Rule::RepeatMany(..)
            | Rule::RepeatMore(..) => false,
            Rule::Concat(rules) => rules[path[0]].field_path_is_refutable(cx, &path[1..]),
            Rule::Or(..) | Rule::Opt(_) => true,
        }
    }

    fn can_be_empty<Pat: MatchesEmpty>(
        self,
        cache: &mut HashMap<Self, MaybeKnown<bool>>,
        cx: &Context<Pat>,
        grammar: &crate::Grammar,
    ) -> MaybeKnown<bool> {
        match cache.entry(self) {
            Entry::Occupied(entry) => return *entry.get(),
            Entry::Vacant(entry) => {
                entry.insert(MaybeKnown::Unknown);
            }
        };
        let r = match cx[self] {
            Rule::Empty | Rule::Opt(_) | Rule::RepeatMany(..) => MaybeKnown::Known(true),
            Rule::Eat(ref pat) => pat.matches_empty(),
            Rule::Call(rule) => grammar.rules[&rule].rule.can_be_empty(cache, cx, grammar),
            Rule::Concat([left, right]) => {
                left.can_be_empty(cache, cx, grammar) & right.can_be_empty(cache, cx, grammar)
            }
            Rule::Or(ref rules) => rules.iter().fold(MaybeKnown::Known(false), |prev, rule| {
                prev | rule.can_be_empty(cache, cx, grammar)
            }),
            Rule::RepeatMore(elem, _) => elem.can_be_empty(cache, cx, grammar),
        };
        match r {
            MaybeKnown::Known(_) => *cache.get_mut(&self).unwrap() = r,
            MaybeKnown::Unknown => {
                cache.remove(&self);
            }
        }
        r
    }

    pub(crate) fn check_non_empty_opt<Pat: MatchesEmpty>(
        self,
        cache: &mut HashMap<IRule, MaybeKnown<bool>>,
        cx: &Context<Pat>,
        grammar: &crate::Grammar,
    ) {
        match cx[self] {
            Rule::Empty | Rule::Eat(_) | Rule::Call(_) => {}
            Rule::Concat([left, right]) => {
                left.check_non_empty_opt(cache, cx, grammar);
                right.check_non_empty_opt(cache, cx, grammar);
            }
            Rule::Or(ref rules) => {
                for rule in rules {
                    rule.check_non_empty_opt(cache, cx, grammar);
                }
            }
            Rule::Opt(rule) => {
                assert_eq!(
                    rule.can_be_empty(cache, cx, grammar),
                    MaybeKnown::Known(false)
                );
                rule.check_non_empty_opt(cache, cx, grammar)
            }
            Rule::RepeatMany(elem, sep) | Rule::RepeatMore(elem, sep) => {
                assert_eq!(
                    elem.can_be_empty(cache, cx, grammar),
                    MaybeKnown::Known(false)
                );
                elem.check_non_empty_opt(cache, cx, grammar);
                if let Some((sep, _)) = sep {
                    sep.check_non_empty_opt(cache, cx, grammar);
                }
            }
        }
    }

    pub(crate) fn check_call_names<Pat>(self, cx: &Context<Pat>, grammar: &crate::Grammar) {
        match cx[self] {
            Rule::Empty | Rule::Eat(_) => {}
            Rule::Call(rule) => {
                assert!(
                    grammar.rules.contains_key(&rule),
                    "no rule named `{}`",
                    cx[rule]
                );
            }
            Rule::Concat([left, right]) => {
                left.check_call_names(cx, grammar);
                right.check_call_names(cx, grammar);
            }
            Rule::Or(ref rules) => {
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

pub trait Folder<Pat: Eq + Hash>: Sized {
    fn cx(&mut self) -> &mut Context<Pat>;
    fn fold_leaf(&mut self, rule: RuleWithNamedFields) -> RuleWithNamedFields {
        rule
    }
    fn fold_concat(
        &mut self,
        left: RuleWithNamedFields,
        right: RuleWithNamedFields,
    ) -> RuleWithNamedFields {
        (left.fold(self) + right.fold(self)).finish(self.cx())
    }
    fn fold_or(
        &mut self,
        mut rules: impl Iterator<Item = RuleWithNamedFields>,
    ) -> RuleWithNamedFields {
        let first = rules.next().unwrap().fold(self);
        rules.fold(first, |or, rule| (or | rule.fold(self)).finish(self.cx()))
    }
    fn fold_opt(&mut self, rule: RuleWithNamedFields) -> RuleWithNamedFields {
        rule.fold(self).opt().finish(self.cx())
    }
    fn fold_repeat_many(
        &mut self,
        elem: RuleWithNamedFields,
        sep: Option<(RuleWithNamedFields, SepKind)>,
    ) -> RuleWithNamedFields {
        let elem = elem.fold(self);
        let sep = sep.map(|(sep, kind)| (sep.fold(self), kind));
        match sep {
            None => elem.repeat_many().finish(self.cx()),
            Some((sep, kind)) => elem.repeat_many_sep(sep, kind).finish(self.cx()),
        }
    }
    fn fold_repeat_more(
        &mut self,
        elem: RuleWithNamedFields,
        sep: Option<(RuleWithNamedFields, SepKind)>,
    ) -> RuleWithNamedFields {
        let elem = elem.fold(self);
        let sep = sep.map(|(sep, kind)| (sep.fold(self), kind));
        match sep {
            None => elem.repeat_more().finish(self.cx()),
            Some((sep, kind)) => elem.repeat_more_sep(sep, kind).finish(self.cx()),
        }
    }
}

impl RuleWithNamedFields {
    // HACK(eddyb) this is pretty expensive, find a better way
    fn filter_fields<'a>(&'a self, i: Option<usize>) -> impl Iterator<Item = (IStr, Field)> + 'a {
        self.fields.iter().filter_map(move |(&name, field)| {
            let paths: IndexMap<_, _> = field
                .paths
                .iter()
                .filter_map(move |(path, subfields)| {
                    if path.first().cloned() == i {
                        Some((path.get(1..).unwrap_or(&[]).to_vec(), subfields.clone()))
                    } else {
                        None
                    }
                })
                .collect();
            if !paths.is_empty() {
                Some((name, Field { paths }))
            } else {
                None
            }
        })
    }

    pub fn fold<Pat: Eq + Hash>(self, folder: &mut impl Folder<Pat>) -> Self {
        let field_rule = |rule, i| RuleWithNamedFields {
            rule,
            fields: self.filter_fields(Some(i)).collect(),
        };
        let mut rule = match folder.cx()[self.rule] {
            Rule::Empty | Rule::Eat(_) | Rule::Call(_) => return folder.fold_leaf(self),
            Rule::Concat([left, right]) => {
                folder.fold_concat(field_rule(left, 0), field_rule(right, 1))
            }
            Rule::Or(ref rules) => {
                // FIXME(eddyb) this is inefficient, but we can't be iterating
                // `rules` while folding, at least not without e.g. an arena.
                let rules = rules.clone();
                folder.fold_or(
                    rules
                        .into_iter()
                        .enumerate()
                        .map(|(i, rule)| field_rule(rule, i)),
                )
            }
            Rule::Opt(rule) => folder.fold_opt(field_rule(rule, 0)),
            Rule::RepeatMany(elem, sep) => folder.fold_repeat_many(
                field_rule(elem, 0),
                sep.map(|(sep, kind)| (field_rule(sep, 1), kind)),
            ),
            Rule::RepeatMore(elem, sep) => folder.fold_repeat_more(
                field_rule(elem, 0),
                sep.map(|(sep, kind)| (field_rule(sep, 1), kind)),
            ),
        };
        rule.fields.extend(self.filter_fields(None));
        rule
    }

    pub fn insert_whitespace<Pat: Eq + Hash>(
        self,
        cx: &mut Context<Pat>,
        whitespace: RuleWithNamedFields,
    ) -> Self {
        assert!(whitespace.fields.is_empty());

        struct WhitespaceInserter<'a, Pat> {
            cx: &'a mut Context<Pat>,
            whitespace: RuleWithNamedFields,
        }

        impl<Pat: Eq + Hash> Folder<Pat> for WhitespaceInserter<'_, Pat> {
            fn cx(&mut self) -> &mut Context<Pat> {
                self.cx
            }
            // FIXME(eddyb) this will insert too many whitespace rules,
            // e.g. `A B? C` becomes `A WS B? WS C`, which when `B` is
            // missing, is `A WS WS C`. Even worse, `A? B` ends up as
            // `A? WS B`, which has an incorrect leading whitespace.
            fn fold_concat(
                &mut self,
                left: RuleWithNamedFields,
                right: RuleWithNamedFields,
            ) -> RuleWithNamedFields {
                (left.fold(self) + self.whitespace.clone() + right.fold(self)).finish(self.cx())
            }
            fn fold_repeat_many(
                &mut self,
                elem: RuleWithNamedFields,
                sep: Option<(RuleWithNamedFields, SepKind)>,
            ) -> RuleWithNamedFields {
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
                elem: RuleWithNamedFields,
                sep: Option<(RuleWithNamedFields, SepKind)>,
            ) -> RuleWithNamedFields {
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
