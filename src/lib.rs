#![deny(rust_2018_idioms)]

use ordermap::{orderset, OrderMap, OrderSet};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::hash::Hash;
use std::iter;
use std::ops::{Add, BitAnd, BitOr};
use std::rc::Rc;

pub struct Grammar<Pat> {
    pub rules: OrderMap<String, RuleWithNamedFields<Pat>>,
}

impl<Pat> Grammar<Pat> {
    pub fn new() -> Self {
        Grammar {
            rules: OrderMap::new(),
        }
    }
    pub fn define(&mut self, name: &str, rule: RuleWithNamedFields<Pat>) {
        self.rules.insert(name.to_string(), rule);
    }
    pub fn extend(&mut self, other: Self) {
        self.rules.extend(other.rules);
    }
    pub fn insert_whitespace(self, whitespace: RuleWithNamedFields<Pat>) -> Self
    where
        Pat: Clone,
    {
        assert!(whitespace.fields.is_empty());

        struct WhitespaceInserter<Pat> {
            whitespace: RuleWithNamedFields<Pat>,
        }

        impl<Pat: Clone> Folder<Pat> for WhitespaceInserter<Pat> {
            // FIXME(eddyb) this will insert too many whitespace rules,
            // e.g. `A B? C` becomes `A WS B? WS C`, which when `B` is
            // missing, is `A WS WS C`. Even worse, `A? B` ends up as
            // `A? WS B`, which has an incorrect leading whitespace.
            fn fold_concat(
                &mut self,
                left: RuleWithNamedFields<Pat>,
                right: RuleWithNamedFields<Pat>,
            ) -> RuleWithNamedFields<Pat> {
                left.fold(self) + self.whitespace.clone() + right.fold(self)
            }
            fn fold_repeat_many(
                &mut self,
                elem: RuleWithNamedFields<Pat>,
                sep: Option<(RuleWithNamedFields<Pat>, SepKind)>,
            ) -> RuleWithNamedFields<Pat> {
                match sep {
                    // A* => A* % WS
                    None => elem
                        .fold(self)
                        .repeat_more(Some((self.whitespace.clone(), SepKind::Simple))),
                    // A* % B => A* % A* % (WS B WS)
                    Some((sep, SepKind::Simple)) => elem.fold(self).repeat_more(Some((
                        self.whitespace.clone() + sep + self.whitespace.clone(),
                        SepKind::Simple,
                    ))),
                    // FIXME(cad97) this will insert too many whitespace rules
                    // A* %% B => ???
                    // Currently, A* %% (WS B WS), which allows trailing whitespace incorrectly
                    Some((sep, SepKind::Trailing)) => {
                        elem.fold(self).repeat_more(Some((
                            self.whitespace.clone() + sep.clone() + self.whitespace.clone(),
                            SepKind::Trailing,
                        )))
                    }
                }
            }
            fn fold_repeat_more(
                &mut self,
                elem: RuleWithNamedFields<Pat>,
                sep: Option<(RuleWithNamedFields<Pat>, SepKind)>,
            ) -> RuleWithNamedFields<Pat> {
                match sep {
                    // A+ => A+ % WS
                    None => elem
                        .fold(self)
                        .repeat_more(Some((self.whitespace.clone(), SepKind::Simple))),
                    // A+ % B => A+ % (WS B WS)
                    Some((sep, SepKind::Simple)) => elem.fold(self).repeat_more(Some((
                        self.whitespace.clone() + sep + self.whitespace.clone(),
                        SepKind::Simple,
                    ))),
                    // A+ %% B => A+ % (WS B WS) (WS B)?
                    Some((sep, SepKind::Trailing)) => {
                        elem.fold(self).repeat_more(Some((
                            self.whitespace.clone() + sep.clone() + self.whitespace.clone(),
                            SepKind::Simple,
                        ))) + (self.whitespace.clone() + sep).opt()
                    }
                }
            }
        }

        let mut inserter = WhitespaceInserter { whitespace };
        Grammar {
            rules: self
                .rules
                .into_iter()
                .map(|(name, rule)| (name, rule.fold(&mut inserter)))
                .collect(),
        }
    }
}

#[derive(Clone)]
pub struct RuleWithNamedFields<Pat> {
    pub rule: Rc<Rule<Pat>>,
    pub fields: OrderMap<String, OrderSet<Vec<usize>>>,
}

pub fn empty<Pat>() -> RuleWithNamedFields<Pat> {
    RuleWithNamedFields {
        rule: Rc::new(Rule::Empty),
        fields: OrderMap::new(),
    }
}
pub fn eat<Pat>(pat: impl Into<Pat>) -> RuleWithNamedFields<Pat> {
    RuleWithNamedFields {
        rule: Rc::new(Rule::Eat(pat.into())),
        fields: OrderMap::new(),
    }
}
pub fn negative_lookahead<Pat>(pat: impl Into<Pat>) -> RuleWithNamedFields<Pat> {
    RuleWithNamedFields {
        rule: Rc::new(Rule::NegativeLookahead(pat.into())),
        fields: OrderMap::new(),
    }
}
pub fn call<Pat>(name: &str) -> RuleWithNamedFields<Pat> {
    RuleWithNamedFields {
        rule: Rc::new(Rule::Call(name.to_string())),
        fields: OrderMap::new(),
    }
}

impl<Pat> RuleWithNamedFields<Pat> {
    pub fn field(mut self, name: &str) -> Self {
        let path = match &*self.rule {
            Rule::RepeatMany(rule, _) | Rule::RepeatMore(rule, _) => match **rule {
                Rule::Eat(_) | Rule::Call(_) => vec![],
                _ => unimplemented!(),
            },
            Rule::Opt(_) => vec![0],
            _ => vec![],
        };
        self.fields.insert(name.to_string(), orderset![path]);
        self
    }
    pub fn opt(mut self) -> Self {
        self.fields = self
            .fields
            .into_iter()
            .map(|(name, paths)| {
                (
                    name,
                    paths
                        .into_iter()
                        .map(|mut path| {
                            path.insert(0, 0);
                            path
                        })
                        .collect(),
                )
            })
            .collect();
        self.rule = Rc::new(Rule::Opt(self.rule));
        self
    }
    pub fn repeat_many(mut self, sep: Option<(Self, SepKind)>) -> Self {
        self.fields = self
            .fields
            .into_iter()
            .map(|(name, paths)| {
                (
                    name,
                    paths
                        .into_iter()
                        .map(|mut path| {
                            path.insert(0, 0);
                            path
                        })
                        .collect(),
                )
            })
            .collect();
        if let Some((sep, _)) = &sep {
            assert!(sep.fields.is_empty());
        }
        self.rule = Rc::new(Rule::RepeatMany(
            self.rule,
            sep.map(|(sep, kind)| (sep.rule, kind)),
        ));
        self
    }
    pub fn repeat_more(mut self, sep: Option<(Self, SepKind)>) -> Self {
        self.fields = self
            .fields
            .into_iter()
            .map(|(name, paths)| {
                (
                    name,
                    paths
                        .into_iter()
                        .map(|mut path| {
                            path.insert(0, 0);
                            path
                        })
                        .collect(),
                )
            })
            .collect();
        if let Some((sep, _)) = &sep {
            assert!(sep.fields.is_empty());
        }
        self.rule = Rc::new(Rule::RepeatMore(
            self.rule,
            sep.map(|(sep, kind)| (sep.rule, kind)),
        ));
        self
    }
}

impl<Pat> Add for RuleWithNamedFields<Pat> {
    type Output = Self;

    fn add(mut self, other: Self) -> Self {
        match (&*self.rule, &*other.rule) {
            (Rule::Empty, _) if self.fields.is_empty() => return other,
            (_, Rule::Empty) if other.fields.is_empty() => return self,
            _ => {}
        }

        self.fields = self
            .fields
            .into_iter()
            .map(|(name, paths)| {
                (
                    name,
                    paths
                        .into_iter()
                        .map(|mut path| {
                            path.insert(0, 0);
                            path
                        })
                        .collect(),
                )
            })
            .collect();
        for (name, paths) in other.fields {
            assert!(!self.fields.contains_key(&name), "duplicate field {}", name);
            self.fields.insert(
                name,
                paths
                    .into_iter()
                    .map(|mut path| {
                        path.insert(0, 1);
                        path
                    })
                    .collect(),
            );
        }
        self.rule = Rc::new(Rule::Concat([self.rule, other.rule]));
        self
    }
}

impl<Pat> BitOr for RuleWithNamedFields<Pat> {
    type Output = Self;

    fn bitor(self, other: Self) -> Self {
        let (old_rules, this, mut fields) = match &*self.rule {
            Rule::Or(rules) => (&rules[..], None, self.fields),
            _ => (&[][..], Some(self), OrderMap::new()),
        };

        let new_rules =
            this.into_iter()
                .chain(iter::once(other))
                .enumerate()
                .map(|(i, rule)| {
                    for (name, paths) in rule.fields {
                        fields.entry(name).or_insert_with(OrderSet::new).extend(
                            paths.into_iter().map(|mut path| {
                                path.insert(0, old_rules.len() + i);
                                path
                            }),
                        );
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

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SepKind {
    Simple,
    Trailing,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Rule<Pat> {
    Empty,
    Eat(Pat),
    NegativeLookahead(Pat),
    Call(String),

    Concat([Rc<Rule<Pat>>; 2]),
    Or(Vec<Rc<Rule<Pat>>>),

    Opt(Rc<Rule<Pat>>),
    RepeatMany(Rc<Rule<Pat>>, Option<(Rc<Rule<Pat>>, SepKind)>),
    RepeatMore(Rc<Rule<Pat>>, Option<(Rc<Rule<Pat>>, SepKind)>),
}

impl<Pat> Rule<Pat> {
    pub fn field_pathset_is_refutable(&self, paths: &OrderSet<Vec<usize>>) -> bool {
        if paths.len() > 1 {
            true
        } else {
            self.field_is_refutable(paths.get_index(0).unwrap())
        }
    }
    pub fn field_is_refutable(&self, path: &[usize]) -> bool {
        match self {
            Rule::Empty
            | Rule::Eat(_)
            | Rule::NegativeLookahead(_)
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
        grammar: &Grammar<Pat>,
    ) -> MaybeKnown<bool>;
}

impl<Pat: Ord + Hash + MatchesEmpty> RcRuleMethods<Pat> for Rc<Rule<Pat>> {
    fn can_be_empty(
        &self,
        cache: &mut HashMap<Self, MaybeKnown<bool>>,
        grammar: &Grammar<Pat>,
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
        grammar: &Grammar<Pat>,
    ) -> MaybeKnown<bool> {
        match self {
            Rule::Empty | Rule::NegativeLookahead(_) | Rule::Opt(_) | Rule::RepeatMany(..) => {
                MaybeKnown::Known(true)
            }
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

    fn check_non_empty_opt(
        &self,
        cache: &mut HashMap<Rc<Self>, MaybeKnown<bool>>,
        grammar: &Grammar<Pat>,
    ) {
        match self {
            Rule::Empty | Rule::Eat(_) | Rule::NegativeLookahead(_) | Rule::Call(_) => {}
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

    fn check_call_names(&self, grammar: &Grammar<Pat>) {
        match self {
            Rule::Empty | Rule::Eat(_) | Rule::NegativeLookahead(_) => {}
            Rule::Call(rule) => {
                assert!(grammar.rules.contains_key(rule), "no rule named `{}`", rule);
            }
            Rule::Concat([left, right]) => {
                left.check_call_names(grammar);
                right.check_call_names(grammar);
            }
            Rule::Or(rules) => {
                for rule in rules {
                    rule.check_call_names(grammar);
                }
            }
            Rule::Opt(rule) => rule.check_call_names(grammar),
            Rule::RepeatMany(elem, sep) | Rule::RepeatMore(elem, sep) => {
                elem.check_call_names(grammar);
                if let Some((sep, _)) = sep {
                    sep.check_call_names(grammar);
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

impl<Pat: Ord + Hash + MatchesEmpty> Grammar<Pat> {
    pub fn check(&self) {
        for rule in self.rules.values() {
            rule.rule.check_call_names(self);
        }

        let mut can_be_empty_cache = HashMap::new();
        for rule in self.rules.values() {
            rule.rule.check_non_empty_opt(&mut can_be_empty_cache, self);
        }
    }
}

pub trait Folder<Pat>: Sized {
    fn fold_leaf(&mut self, rule: RuleWithNamedFields<Pat>) -> RuleWithNamedFields<Pat> {
        rule
    }
    fn fold_concat(
        &mut self,
        left: RuleWithNamedFields<Pat>,
        right: RuleWithNamedFields<Pat>,
    ) -> RuleWithNamedFields<Pat> {
        left.fold(self) + right.fold(self)
    }
    fn fold_or(
        &mut self,
        rules: impl Iterator<Item = RuleWithNamedFields<Pat>>,
    ) -> RuleWithNamedFields<Pat> {
        let mut rules = rules.map(|rule| rule.fold(self));
        let first = rules.next().unwrap();
        rules.fold(first, |or, rule| or | rule)
    }
    fn fold_opt(&mut self, rule: RuleWithNamedFields<Pat>) -> RuleWithNamedFields<Pat> {
        rule.fold(self).opt()
    }
    fn fold_repeat_many(
        &mut self,
        elem: RuleWithNamedFields<Pat>,
        sep: Option<(RuleWithNamedFields<Pat>, SepKind)>,
    ) -> RuleWithNamedFields<Pat> {
        elem.fold(self)
            .repeat_many(sep.map(|(sep, kind)| (sep.fold(self), kind)))
    }
    fn fold_repeat_more(
        &mut self,
        elem: RuleWithNamedFields<Pat>,
        sep: Option<(RuleWithNamedFields<Pat>, SepKind)>,
    ) -> RuleWithNamedFields<Pat> {
        elem.fold(self)
            .repeat_more(sep.map(|(sep, kind)| (sep.fold(self), kind)))
    }
}

impl<Pat> RuleWithNamedFields<Pat> {
    // HACK(eddyb) this is pretty expensive, find a better way
    fn filter_fields<'a>(
        &'a self,
        field: Option<usize>,
    ) -> impl Iterator<Item = (String, OrderSet<Vec<usize>>)> + 'a {
        self.fields.iter().filter_map(move |(name, paths)| {
            let paths: OrderSet<_> = paths
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
                Some((name.clone(), paths))
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
            Rule::Empty | Rule::Eat(_) | Rule::NegativeLookahead(_) | Rule::Call(_) => {
                return folder.fold_leaf(self)
            }
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
}

/// Construct a (meta-)grammar for parsing a grammar.
pub fn grammar_grammar<Pat>() -> Grammar<Pat>
where
    Pat: Clone
        + From<&'static str>
        + From<std::ops::RangeInclusive<char>>
        + From<std::ops::RangeFull>,
{
    // HACK(eddyb) more explicit subset of the grammar, for bootstrapping.
    macro_rules! rule {
        ({ $start:tt ..= $end:tt }) => {
            eat($start..=$end)
        };
        ({ ! $pat:tt }) => {
            negative_lookahead($pat)
        };
        ({ ! $start:tt ..= $end:tt }) => {
            negative_lookahead($start..=$end)
        };
        ($rule:ident) => {
            call(stringify!($rule))
        };
        ({ $name:ident : $rule:tt }) => {
            rule!($rule).field(stringify!($name))
        };
        ({ $rule:tt ? }) => {
            rule!($rule).opt()
        };
        ({ $elem:tt * }) => {
            rule!($elem).repeat_many(None)
        };
        ({ $elem:tt + }) => {
            rule!($elem).repeat_more(None)
        };
        ({ $elem:tt + % $sep:tt }) => {
            rule!($elem).repeat_more(Some((rule!($sep), SepKind::Simple)))
        };
        ({ $rule0:tt $(| $rule:tt)+ }) => {
            rule!($rule0) $(| rule!($rule))+
        };
        ({ $rule0:tt $($rule:tt)* }) => {
            rule!($rule0) $(+ rule!($rule))*
        };
        ($pat:expr) => {
            eat($pat)
        };
    }

    macro_rules! grammar {
        ($($rule_name:ident = $($rule:tt)|+;)*) => ({
            let mut grammar = Grammar::new();
            $(grammar.define(stringify!($rule_name), rule!({ $($rule)|+ }));)*
            grammar
        })
    }

    let mut grammar = grammar! {
        // Lexical grammar.
        Whitespace = {
            {{
                " " | "\t" | "\n" | "\r" |
                { "//" {{ {!"\n"} .. }*} "\n" } |
                { "/*" {{ {!"*/"} .. }*} "*/" }
            }*}
            {!" "} {!"\t"} {!"\n"} {!"\r"} {!"//"} {!"/*"}
        };
        Shebang = { "#!" {{ {!"\n"} .. }*} "\n" };

        IdentStart = {'a'..='z'} | {'A'..='Z'} | "_";
        IdentCont = IdentStart | {'0'..='9'};
        NotIdent = { {!'a'..='z'} {!'A'..='Z'} {!"_"} {!'0'..='9'} };
        Ident = { IdentStart {IdentCont*} NotIdent };

        StrLit = { "\"" {{ { {!"\\"} {!"\""} .. } | { "\\" Escape } }*} "\"" };
        CharLit = { "'" { { {!"\\"} {!"'"} .. } | { "\\" Escape } } "'" };
        Escape = "t" | "n" | "r" | "\\" | "'" | "\"";
    };

    grammar.extend(
        grammar! {
            // Main grammar.
            Grammar = { {Shebang?} {rules:{RuleDef*}} Whitespace };
            RuleDef = { {name:Ident} "=" {rule:Or} ";" };
            Or = {{"|"?} {rules:{Concat+ % "|"}}};
            Concat = {rules:{Rule+}};
            Rule = { {{ {field:Ident} ":" }?} {rule:Primary} {{modifier:Modifier}?} };
            Primary =
                {Eat:Pattern} |
                {NegativeLookahead:{ "!" {pat:Pattern} }} |
                {Call:Ident} |
                {Group:{ "{" {{or:Or}?} "}" }};
            Modifier =
                {Opt:"?"} |
                {Repeat:{ {repeat:Repeat} {{ {kind:SepKind} {sep:Primary} }?} }};
            Repeat =
                {Many:"*"} |
                {More:"+"};
            SepKind =
                {Simple:"%"} |
                {Trailing:{"%" "%"}}; // HACK(CAD97): should be "%%" once gll no longer string roundtrips
            Pattern =
                {Str:StrLit} |
                {CharRange:{ {{start:CharLit}?} ".." {{end:CharLit}?} }} |
                {CharRangeInclusive:{ {{start:CharLit}?} "..=" {end:CharLit} }};
        }
        .insert_whitespace(call("Whitespace")),
    );

    grammar
}
