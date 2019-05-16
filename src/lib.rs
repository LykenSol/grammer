#![deny(rust_2018_idioms)]

use crate::context::{Context, IStr};
use indexmap::IndexMap;
use std::collections::HashMap;
use std::hash::Hash;

pub mod context;
pub mod rule;

pub struct Grammar<Pat> {
    pub rules: IndexMap<IStr, rule::RuleWithNamedFields<Pat>>,
}

impl<Pat> Grammar<Pat> {
    pub fn new() -> Self {
        Grammar {
            rules: IndexMap::new(),
        }
    }
    pub fn define(&mut self, name: IStr, rule: rule::RuleWithNamedFields<Pat>) {
        self.rules.insert(name, rule);
    }
    pub fn extend(&mut self, other: Self) {
        self.rules.extend(other.rules);
    }
    pub fn insert_whitespace(
        self,
        cx: &mut Context<Pat>,
        whitespace: rule::RuleWithNamedFields<Pat>,
    ) -> Self
    where
        Pat: Clone,
    {
        Grammar {
            rules: self
                .rules
                .into_iter()
                .map(|(name, rule)| (name, rule.insert_whitespace(cx, whitespace.clone())))
                .collect(),
        }
    }
}

impl<Pat: Ord + Hash + rule::MatchesEmpty> Grammar<Pat> {
    pub fn check(&self, cx: &Context<Pat>) {
        for rule in self.rules.values() {
            rule.rule.check_call_names(cx, self);
        }

        let mut can_be_empty_cache = HashMap::new();
        for rule in self.rules.values() {
            rule.rule.check_non_empty_opt(&mut can_be_empty_cache, self);
        }
    }
}

/// Construct a (meta-)grammar for parsing a grammar.
pub fn grammar_grammar<Pat>(cx: &mut Context<Pat>) -> Grammar<Pat>
where
    Pat: Clone + From<&'static str>,
{
    use crate::rule::*;

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
            rule!($elem).repeat_many()
        };
        ({ $elem:tt + }) => {
            rule!($elem).repeat_more()
        };
        ({ $elem:tt + % $sep:tt }) => {
            rule!($elem).repeat_more_sep(rule!($sep), SepKind::Simple)
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
            $(grammar.define(
                cx.intern(stringify!($rule_name)),
                rule!({ $($rule)|+ }).finish(cx),
            );)*
            grammar
        })
    }

    // Main grammar.
    let mut grammar = grammar! {
        Grammar = { FileStart {rules:{RuleDef*}} FileEnd };
        RuleDef = { {name:Ident} "=" {rule:Or} ";" };
        Or = {{"|"?} {rules:{Concat+ % "|"}}};
        Concat = {rules:{Rule+}};
        Rule = { {{ {field:Ident} ":" }?} {rule:Primary} {{modifier:Modifier}?} };
        Primary =
            {Eat:Pattern} |
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
            // HACK(eddyb) should be "%%", but `rustc`'s `proc_macro` server doesn't
            // always preserve jointness, except within multi-character Rust operators.
            {Trailing:{"%" "%"}};
        Pattern =
            {Str:StrLit} |
            {CharRange:{ {{start:CharLit}?} ".." {{end:CharLit}?} }} |
            {CharRangeInclusive:{ {{start:CharLit}?} "..=" {end:CharLit} }};
    };

    // Lexical fragment of the grammar.
    grammar.extend(grammar! {
        FileStart = "";
        FileEnd = "";

        Ident = IDENT;

        // FIXME(eddyb) restrict literals, once `proc_macro` allows it.
        StrLit = LITERAL;
        CharLit = LITERAL;
    });

    grammar
}
