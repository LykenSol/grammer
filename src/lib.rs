#![deny(unsafe_code)]
#![deny(rust_2018_idioms)]

// NOTE only these two modules can and do contain unsafe code.
#[allow(unsafe_code)]
mod high;
#[allow(unsafe_code)]
mod indexing_str;

#[forbid(unsafe_code)]
pub mod bruteforce;
#[forbid(unsafe_code)]
pub mod context;
#[forbid(unsafe_code)]
pub mod forest;
#[forbid(unsafe_code)]
pub mod input;
#[forbid(unsafe_code)]
pub mod lyg;
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
