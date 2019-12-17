#![deny(unsafe_code)]
#![deny(rust_2018_idioms)]

// NOTE only these two modules can and do contain unsafe code.
#[allow(unsafe_code)]
mod high;
#[allow(unsafe_code)]
mod indexing_str;

#[forbid(unsafe_code)]
pub mod context;
#[forbid(unsafe_code)]
pub mod forest;
#[forbid(unsafe_code)]
pub mod input;
#[forbid(unsafe_code)]
pub mod parser;
#[forbid(unsafe_code)]
pub mod proc_macro;
#[forbid(unsafe_code)]
pub mod rule;
#[forbid(unsafe_code)]
pub mod scannerless;

// HACK(eddyb) this contains impls for types in `proc_macro`, which depend on
// `input`, collapse this back into `proc_macro`.
#[forbid(unsafe_code)]
mod proc_macro_input;

// FIXME(eddyb) maybe put the rest of this file into submodules?

use crate::context::{Context, IStr};
use indexmap::IndexMap;
use std::collections::HashMap;
use std::hash::Hash;

use std::ops::Range;

trait RangeExt<Idx> {
    fn split_at(&self, idx: Idx) -> (Range<Idx>, Range<Idx>);
    fn join(&self, other: Range<Idx>) -> Result<Range<Idx>, Box<dyn std::error::Error>>;
}

impl<Idx> RangeExt<Idx> for Range<Idx>
where
    Idx: Copy + Eq,
{
    fn split_at(&self, idx: Idx) -> (Range<Idx>, Range<Idx>) {
        (self.start..idx, idx..self.end)
    }

    fn join(&self, other: Range<Idx>) -> Result<Range<Idx>, Box<dyn std::error::Error>> {
        if self.end != other.start {
            return Err("ranges must be adjacent".into());
        }
        Ok(self.start..other.end)
    }
}

pub struct Grammar {
    pub rules: IndexMap<IStr, rule::RuleWithFields>,
}

impl Grammar {
    pub fn new() -> Self {
        Grammar {
            rules: IndexMap::new(),
        }
    }
    pub fn define(&mut self, name: IStr, rule: rule::RuleWithFields) {
        self.rules.insert(name, rule);
    }
    pub fn extend(&mut self, other: Self) {
        self.rules.extend(other.rules);
    }
    pub fn insert_whitespace<Pat: Eq + Hash>(
        self,
        cx: &Context<Pat>,
        whitespace: rule::RuleWithFields,
    ) -> Self {
        Grammar {
            rules: self
                .rules
                .into_iter()
                .map(|(name, rule)| (name, rule.insert_whitespace(cx, whitespace)))
                .collect(),
        }
    }
}

impl Grammar {
    pub fn check<Pat: rule::MatchesEmpty>(&self, cx: &Context<Pat>) {
        for rule in self.rules.values() {
            rule.rule.check_call_names(cx, self);
        }

        let mut can_be_empty_cache = HashMap::new();
        for rule in self.rules.values() {
            rule.rule
                .check_non_empty_opt(&mut can_be_empty_cache, cx, self);
        }
    }
}

/// Construct a (meta-)grammar for parsing a grammar.
pub fn grammar_grammar<Pat: Eq + Hash + From<&'static str>>(cx: &Context<Pat>) -> Grammar {
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
