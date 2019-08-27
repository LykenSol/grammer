use crate::context::{Context, IFields, IRule, IStr};
use crate::forest::NodeShape;
use indexmap::IndexMap;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::iter;
use std::ops::{Add, BitAnd, BitOr};

#[derive(Copy, Clone)]
pub struct RuleWithFields {
    pub rule: IRule,
    pub fields: IFields,
}

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

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Field {
    pub name: IStr,
    pub sub: IFields,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Fields {
    Leaf(Option<Field>),
    Aggregate(Vec<IFields>),
}

impl Fields {
    fn aggregate<Pat: Eq + Hash>(
        cx: &Context<Pat>,
        mut children: impl Iterator<Item = IFields>,
    ) -> IFields {
        let empty_leaf = cx.intern(Fields::Leaf(None));
        let mut empty_count = 0;
        for child in &mut children {
            if child != empty_leaf {
                return cx.intern(Fields::Aggregate(
                    iter::repeat(empty_leaf)
                        .take(empty_count)
                        .chain(iter::once(child))
                        .chain(children)
                        .collect(),
                ));
            }

            empty_count += 1;
        }
        empty_leaf
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

    impl Start for RuleWithFields {
        type Out = RuleWithFields;

        fn start(self) -> Self::Out {
            self
        }
    }

    pub trait Finish<Pat> {
        fn finish(self, cx: &Context<Pat>) -> RuleWithFields;
    }

    impl<Pat> Finish<Pat> for RuleWithFields {
        fn finish(self, _cx: &Context<Pat>) -> RuleWithFields {
            self
        }
    }

    pub struct Empty;

    impl<Pat: Eq + Hash> Finish<Pat> for Empty {
        fn finish(self, cx: &Context<Pat>) -> RuleWithFields {
            RuleWithFields {
                rule: cx.intern(Rule::Empty),
                fields: cx.intern(Fields::Leaf(None)),
            }
        }
    }

    pub struct Eat<Pat>(Pat);

    impl<Pat: Eq + Hash> Finish<Pat> for Eat<Pat> {
        fn finish(self, cx: &Context<Pat>) -> RuleWithFields {
            RuleWithFields {
                rule: cx.intern(Rule::Eat(self.0)),
                fields: cx.intern(Fields::Leaf(None)),
            }
        }
    }

    pub struct Call<'a>(&'a str);

    impl<Pat: Eq + Hash> Finish<Pat> for Call<'_> {
        fn finish(self, cx: &Context<Pat>) -> RuleWithFields {
            RuleWithFields {
                rule: cx.intern(Rule::Call(cx.intern(self.0))),
                fields: cx.intern(Fields::Leaf(None)),
            }
        }
    }

    pub struct Field<'a, R>(R, &'a str);

    impl<Pat: Eq + Hash, R: Finish<Pat>> Finish<Pat> for Field<'_, R> {
        fn finish(self, cx: &Context<Pat>) -> RuleWithFields {
            let rule = self.0.finish(cx);
            RuleWithFields {
                rule: rule.rule,
                fields: cx.intern(Fields::Leaf(Some(super::Field {
                    name: cx.intern(self.1),
                    sub: rule.fields,
                }))),
            }
        }
    }

    pub struct Opt<R>(R);

    impl<Pat: Eq + Hash, R: Finish<Pat>> Finish<Pat> for Opt<R> {
        fn finish(self, cx: &Context<Pat>) -> RuleWithFields {
            let rule = self.0.finish(cx);
            RuleWithFields {
                rule: cx.intern(Rule::Opt(rule.rule)),
                fields: Fields::aggregate(cx, iter::once(rule.fields)),
            }
        }
    }

    pub struct RepeatMany<E>(E);

    impl<Pat: Eq + Hash, E: Finish<Pat>> Finish<Pat> for RepeatMany<E> {
        fn finish(self, cx: &Context<Pat>) -> RuleWithFields {
            let elem = self.0.finish(cx);
            RuleWithFields {
                rule: cx.intern(Rule::RepeatMany(elem.rule, None)),
                fields: Fields::aggregate(cx, iter::once(elem.fields)),
            }
        }
    }

    pub struct RepeatManySep<E, S>(E, S, SepKind);

    impl<Pat: Eq + Hash, E: Finish<Pat>, S: Finish<Pat>> Finish<Pat> for RepeatManySep<E, S> {
        fn finish(self, cx: &Context<Pat>) -> RuleWithFields {
            let elem = self.0.finish(cx);
            let sep = self.1.finish(cx);
            assert_eq!(cx[sep.fields], Fields::Leaf(None));
            RuleWithFields {
                rule: cx.intern(Rule::RepeatMany(elem.rule, Some((sep.rule, self.2)))),
                fields: Fields::aggregate(cx, iter::once(elem.fields)),
            }
        }
    }

    pub struct RepeatMore<E>(E);

    impl<Pat: Eq + Hash, E: Finish<Pat>> Finish<Pat> for RepeatMore<E> {
        fn finish(self, cx: &Context<Pat>) -> RuleWithFields {
            let elem = self.0.finish(cx);
            RuleWithFields {
                rule: cx.intern(Rule::RepeatMore(elem.rule, None)),
                fields: Fields::aggregate(cx, iter::once(elem.fields)),
            }
        }
    }

    pub struct RepeatMoreSep<E, S>(E, S, SepKind);

    impl<Pat: Eq + Hash, E: Finish<Pat>, S: Finish<Pat>> Finish<Pat> for RepeatMoreSep<E, S> {
        fn finish(self, cx: &Context<Pat>) -> RuleWithFields {
            let elem = self.0.finish(cx);
            let sep = self.1.finish(cx);
            assert_eq!(cx[sep.fields], Fields::Leaf(None));
            RuleWithFields {
                rule: cx.intern(Rule::RepeatMore(elem.rule, Some((sep.rule, self.2)))),
                fields: Fields::aggregate(cx, iter::once(elem.fields)),
            }
        }
    }

    pub struct Concat<A, B>(A, B);

    impl<Pat: Eq + Hash, A: Finish<Pat>, B: Finish<Pat>> Finish<Pat> for Concat<A, B> {
        fn finish(self, cx: &Context<Pat>) -> RuleWithFields {
            let a = self.0.finish(cx);
            let b = self.1.finish(cx);

            match (&cx[a.rule], &cx[b.rule]) {
                (Rule::Empty, _) if cx[a.fields] == Fields::Leaf(None) => return b,
                (_, Rule::Empty) if cx[b.fields] == Fields::Leaf(None) => return a,
                _ => {}
            }

            RuleWithFields {
                rule: cx.intern(Rule::Concat([a.rule, b.rule])),
                fields: Fields::aggregate(cx, [a.fields, b.fields].iter().cloned()),
            }
        }
    }

    pub struct Or<A, B>(A, B);

    impl<Pat: Eq + Hash, A: Finish<Pat>, B: Finish<Pat>> Finish<Pat> for Or<A, B> {
        fn finish(self, cx: &Context<Pat>) -> RuleWithFields {
            let a = self.0.finish(cx);
            let b = self.1.finish(cx);

            match (&cx[a.rule], &cx[a.fields]) {
                (Rule::Or(a_rules), Fields::Leaf(None)) => RuleWithFields {
                    rule: cx.intern(Rule::Or(
                        a_rules.iter().cloned().chain(iter::once(b.rule)).collect(),
                    )),
                    fields: Fields::aggregate(
                        cx,
                        iter::repeat(a.fields)
                            .take(a_rules.len())
                            .chain(iter::once(b.fields)),
                    ),
                },
                (Rule::Or(a_rules), Fields::Aggregate(a_children)) => RuleWithFields {
                    rule: cx.intern(Rule::Or(
                        a_rules.iter().cloned().chain(iter::once(b.rule)).collect(),
                    )),
                    fields: Fields::aggregate(
                        cx,
                        a_children.iter().cloned().chain(iter::once(b.fields)),
                    ),
                },
                _ => RuleWithFields {
                    rule: cx.intern(Rule::Or(vec![a.rule, b.rule])),
                    fields: Fields::aggregate(cx, [a.fields, b.fields].iter().cloned()),
                },
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
        pub fn finish<Pat>(self, cx: &Context<Pat>) -> RuleWithFields
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
    /// `RuleWithFields` and `Build<R>`, instead of just one of them.
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
    builder_impls!(impl<> RuleWithFields);
}

pub use self::build::{call, eat, empty};

impl IRule {
    pub fn node_desc<Pat>(self, cx: &Context<Pat>) -> String
    where
        Pat: fmt::Debug,
    {
        match cx[self] {
            Rule::Empty => "".to_string(),
            Rule::Eat(ref pat) => format!("{:?}", pat),
            Rule::Call(r) => cx[r].to_string(),
            Rule::Concat([left, right]) => {
                format!("({} {})", left.node_desc(cx), right.node_desc(cx))
            }
            Rule::Or(ref cases) => {
                assert!(cases.len() > 1);
                let mut desc = format!("({}", cases[0].node_desc(cx));
                for rule in &cases[1..] {
                    desc += " | ";
                    desc += &rule.node_desc(cx);
                }
                desc + ")"
            }
            Rule::Opt(rule) => format!("{}?", rule.node_desc(cx)),
            Rule::RepeatMany(elem, None) => format!("{}*", elem.node_desc(cx)),
            Rule::RepeatMany(elem, Some((sep, SepKind::Simple))) => {
                format!("{}* % {}", elem.node_desc(cx), sep.node_desc(cx))
            }
            Rule::RepeatMany(elem, Some((sep, SepKind::Trailing))) => {
                format!("{}* %% {}", elem.node_desc(cx), sep.node_desc(cx))
            }
            Rule::RepeatMore(elem, None) => format!("{}+", elem.node_desc(cx)),
            Rule::RepeatMore(elem, Some((sep, SepKind::Simple))) => {
                format!("{}+ % {}", elem.node_desc(cx), sep.node_desc(cx))
            }
            Rule::RepeatMore(elem, Some((sep, SepKind::Trailing))) => {
                format!("{}+ %% {}", elem.node_desc(cx), sep.node_desc(cx))
            }
        }
    }

    pub fn node_shape<Pat: Eq + Hash>(
        self,
        cx: &Context<Pat>,
        named_rules: Option<&IndexMap<IStr, RuleWithFields>>,
    ) -> NodeShape<Self> {
        match cx[self] {
            Rule::Empty | Rule::Eat(_) => NodeShape::Opaque,
            Rule::Call(name) => match named_rules.map(|rules| &rules[&name]) {
                Some(rule) if cx[rule.fields] != Fields::Leaf(None) => NodeShape::Alias(rule.rule),
                _ => NodeShape::Opaque,
            },
            Rule::Concat([left, right]) => NodeShape::Split(left, right),
            Rule::Or(_) => NodeShape::Choice,
            Rule::Opt(rule) => NodeShape::Opt(rule),
            Rule::RepeatMany(elem, sep) => NodeShape::Opt(cx.intern(Rule::RepeatMore(elem, sep))),
            Rule::RepeatMore(rule, None) => {
                NodeShape::Split(rule, cx.intern(Rule::RepeatMany(rule, None)))
            }
            Rule::RepeatMore(elem, Some((sep, SepKind::Simple))) => NodeShape::Split(
                elem,
                cx.intern(Rule::Opt(cx.intern(Rule::Concat([sep, self])))),
            ),
            Rule::RepeatMore(elem, Some((sep, SepKind::Trailing))) => NodeShape::Split(
                elem,
                cx.intern(Rule::Opt(cx.intern(Rule::Concat([
                    sep,
                    cx.intern(Rule::RepeatMany(elem, Some((sep, SepKind::Trailing)))),
                ])))),
            ),
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
                    &cx[rule]
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

pub trait Folder<'cx, Pat: 'cx + Eq + Hash>: Sized {
    fn cx(&self) -> &'cx Context<Pat>;
    fn fold_leaf(&mut self, rule: RuleWithFields) -> RuleWithFields {
        rule
    }
    fn fold_concat(&mut self, left: RuleWithFields, right: RuleWithFields) -> RuleWithFields {
        (left.fold(self) + right.fold(self)).finish(self.cx())
    }
    fn fold_or(&mut self, mut rules: impl Iterator<Item = RuleWithFields>) -> RuleWithFields {
        let first = rules.next().unwrap().fold(self);
        rules.fold(first, |or, rule| (or | rule.fold(self)).finish(self.cx()))
    }
    fn fold_opt(&mut self, rule: RuleWithFields) -> RuleWithFields {
        rule.fold(self).opt().finish(self.cx())
    }
    fn fold_repeat_many(
        &mut self,
        elem: RuleWithFields,
        sep: Option<(RuleWithFields, SepKind)>,
    ) -> RuleWithFields {
        let elem = elem.fold(self);
        let sep = sep.map(|(sep, kind)| (sep.fold(self), kind));
        match sep {
            None => elem.repeat_many().finish(self.cx()),
            Some((sep, kind)) => elem.repeat_many_sep(sep, kind).finish(self.cx()),
        }
    }
    fn fold_repeat_more(
        &mut self,
        elem: RuleWithFields,
        sep: Option<(RuleWithFields, SepKind)>,
    ) -> RuleWithFields {
        let elem = elem.fold(self);
        let sep = sep.map(|(sep, kind)| (sep.fold(self), kind));
        match sep {
            None => elem.repeat_more().finish(self.cx()),
            Some((sep, kind)) => elem.repeat_more_sep(sep, kind).finish(self.cx()),
        }
    }
}

impl RuleWithFields {
    pub fn fold<'cx, Pat: 'cx + Eq + Hash>(self, folder: &mut impl Folder<'cx, Pat>) -> Self {
        let cx = folder.cx();
        let aggregate_fields = match cx[self.fields] {
            Fields::Leaf(Some(field)) => {
                let mut rule = RuleWithFields {
                    rule: self.rule,
                    fields: field.sub,
                }
                .fold(folder);
                rule.fields = cx.intern(Fields::Leaf(Some(Field {
                    name: field.name,
                    sub: rule.fields,
                })));
                return rule;
            }
            Fields::Leaf(None) => &[][..],
            Fields::Aggregate(ref children) => children,
        };
        let field_rule = |rule, i| RuleWithFields {
            rule,
            fields: aggregate_fields
                .get(i)
                .cloned()
                .unwrap_or_else(|| cx.intern(Fields::Leaf(None))),
        };
        match cx[self.rule] {
            Rule::Empty | Rule::Eat(_) | Rule::Call(_) => return folder.fold_leaf(self),
            Rule::Concat([left, right]) => {
                folder.fold_concat(field_rule(left, 0), field_rule(right, 1))
            }
            Rule::Or(ref rules) => folder.fold_or(
                rules
                    .iter()
                    .enumerate()
                    .map(|(i, &rule)| field_rule(rule, i)),
            ),
            Rule::Opt(rule) => folder.fold_opt(field_rule(rule, 0)),
            Rule::RepeatMany(elem, sep) => folder.fold_repeat_many(
                field_rule(elem, 0),
                sep.map(|(sep, kind)| (field_rule(sep, 1), kind)),
            ),
            Rule::RepeatMore(elem, sep) => folder.fold_repeat_more(
                field_rule(elem, 0),
                sep.map(|(sep, kind)| (field_rule(sep, 1), kind)),
            ),
        }
    }

    pub fn insert_whitespace<Pat: Eq + Hash>(
        self,
        cx: &Context<Pat>,
        whitespace: RuleWithFields,
    ) -> Self {
        assert_eq!(cx[whitespace.fields], Fields::Leaf(None));

        struct WhitespaceInserter<'cx, Pat> {
            cx: &'cx Context<Pat>,
            whitespace: RuleWithFields,
        }

        impl<'cx, Pat: Eq + Hash> Folder<'cx, Pat> for WhitespaceInserter<'cx, Pat> {
            fn cx(&self) -> &'cx Context<Pat> {
                self.cx
            }
            // FIXME(eddyb) this will insert too many whitespace rules,
            // e.g. `A B? C` becomes `A WS B? WS C`, which when `B` is
            // missing, is `A WS WS C`. Even worse, `A? B` ends up as
            // `A? WS B`, which has an incorrect leading whitespace.
            fn fold_concat(
                &mut self,
                left: RuleWithFields,
                right: RuleWithFields,
            ) -> RuleWithFields {
                (left.fold(self) + self.whitespace + right.fold(self)).finish(self.cx())
            }
            fn fold_repeat_many(
                &mut self,
                elem: RuleWithFields,
                sep: Option<(RuleWithFields, SepKind)>,
            ) -> RuleWithFields {
                let elem = elem.fold(self);
                let sep = sep.map(|(sep, kind)| (sep.fold(self), kind));
                match sep {
                    // A* => A* % WS
                    None => elem
                        .repeat_more_sep(self.whitespace, SepKind::Simple)
                        .finish(self.cx),
                    // A* % B => A* % (WS B WS)
                    Some((sep, SepKind::Simple)) => elem
                        .repeat_more_sep(self.whitespace + sep + self.whitespace, SepKind::Simple)
                        .finish(self.cx),
                    // FIXME(cad97) this will insert too many whitespace rules
                    // A* %% B => ???
                    // Currently, A* %% (WS B WS), which allows trailing whitespace incorrectly
                    Some((sep, SepKind::Trailing)) => elem
                        .repeat_more_sep(self.whitespace + sep + self.whitespace, SepKind::Trailing)
                        .finish(self.cx),
                }
            }
            fn fold_repeat_more(
                &mut self,
                elem: RuleWithFields,
                sep: Option<(RuleWithFields, SepKind)>,
            ) -> RuleWithFields {
                let elem = elem.fold(self);
                let sep = sep.map(|(sep, kind)| (sep.fold(self), kind));
                match sep {
                    // A+ => A+ % WS
                    None => elem
                        .repeat_more_sep(self.whitespace, SepKind::Simple)
                        .finish(self.cx),
                    // A+ % B => A+ % (WS B WS)
                    Some((sep, SepKind::Simple)) => elem
                        .fold(self)
                        .repeat_more_sep(self.whitespace + sep + self.whitespace, SepKind::Simple)
                        .finish(self.cx),
                    // A+ %% B => A+ % (WS B WS) (WS B)?
                    Some((sep, SepKind::Trailing)) => (elem
                        .repeat_more_sep(self.whitespace + sep + self.whitespace, SepKind::Simple)
                        + (self.whitespace + sep).opt())
                    .finish(self.cx),
                }
            }
        }

        self.fold(&mut WhitespaceInserter { cx, whitespace })
    }
}
