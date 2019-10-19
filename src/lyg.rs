use crate::context::Context;
use crate::forest::dynamic::handle;
use crate::parser::ParseError;
use crate::proc_macro::{FlatToken, Pat as PMPat, Span, TokenStream};
use crate::rule;
use crate::scannerless::Pat as SPat;
use crate::Grammar;
use std::hash::Hash;
use std::ops::Bound;

/// Construct a (meta-)grammar for parsing a `lyg` grammar.
pub fn grammar<Pat: Eq + Hash + From<&'static str>>(cx: &Context<Pat>) -> Grammar {
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

type Handle<'a, 'b, 'i> = crate::forest::dynamic::Handle<'a, 'b, 'i, PMPat, TokenStream>;

pub fn parse<Pat: Eq + Hash + From<SPat>>(
    cx: &Context<Pat>,
    stream: TokenStream,
) -> Result<Grammar, ParseError<Span, PMPat>> {
    let lyg_cx = &crate::proc_macro::Context::new();
    let mut lyg_grammar;

    let g = {
        let cx = lyg_cx;
        lyg_grammar = crate::proc_macro::builtin(cx);
        lyg_grammar.extend(grammar(cx));
        crate::bruteforce::parse(cx, &lyg_grammar, cx.intern("Grammar"), stream.clone())
    };

    let mut grammar = Grammar::new();
    g?.with(|g| {
        handle!(let { rules } = g);
        for rule_def in rules.as_list() {
            handle!(let { name, rule } = rule_def.unwrap());
            let name = match name.source() {
                [FlatToken::Ident(ident)] => ident.to_string(),
                _ => unreachable!(),
            };
            grammar.define(cx.intern(&name[..]), lower_or(rule, cx));
        }
    });
    Ok(grammar)
}

fn lower_or<Pat: Eq + Hash + From<SPat>>(
    this: Handle<'_, '_, '_>,
    cx: &Context<Pat>,
) -> rule::RuleWithFields {
    handle!(let { rules } = this);
    let mut rules = rules.as_list().map(|rule| rule.unwrap());
    let first = lower_concat(rules.next().unwrap(), cx);
    rules.fold(first, |a, b| (a | lower_concat(b, cx)).finish(cx))
}

fn lower_concat<Pat: Eq + Hash + From<SPat>>(
    this: Handle<'_, '_, '_>,
    cx: &Context<Pat>,
) -> rule::RuleWithFields {
    handle!(let { rules } = this);
    rules
        .as_list()
        .map(|rule| rule.unwrap())
        .fold(rule::empty().finish(cx), |a, b| {
            (a + lower_rule(b, cx)).finish(cx)
        })
}

fn lower_rule<Pat: Eq + Hash + From<SPat>>(
    this: Handle<'_, '_, '_>,
    cx: &Context<Pat>,
) -> rule::RuleWithFields {
    handle!(let { rule } = this);
    let mut rule = lower_primary(rule, cx);
    handle!(if let { modifier } = this {
        rule = lower_modifier(modifier, cx, rule);
    });
    handle!(if let { field } = this {
        let field = match field.source() {
            [FlatToken::Ident(ident)] => ident.to_string(),
            _ => unreachable!(),
        };
        rule = rule.field(&field).finish(cx);
    });
    rule
}

fn lower_primary<Pat: Eq + Hash + From<SPat>>(
    this: Handle<'_, '_, '_>,
    cx: &Context<Pat>,
) -> rule::RuleWithFields {
    handle!(match this {
        {Eat:pat} => rule::eat(lower_pattern(pat)).finish(cx),
        {Call:name} => {
            let name = match name.source() {
                [FlatToken::Ident(ident)] => ident.to_string(),
                _ => unreachable!(),
            };
            rule::call(&name).finish(cx)
        },
        {Group:{ or }} => lower_or(or, cx),
        {Group:_} => rule::empty().finish(cx),
    })
}

fn lower_modifier<Pat: Eq + Hash + From<SPat>>(
    this: Handle<'_, '_, '_>,
    cx: &Context<Pat>,
    rule: rule::RuleWithFields,
) -> rule::RuleWithFields {
    handle!(match this {
        {Opt:_} => rule.opt().finish(cx),
        {Repeat:{ repeat, sep, kind }} => {
            let repeat = repeat;
            let sep = lower_primary(sep, cx);
            let kind = lower_sep_kind(kind);
            handle!(match repeat {
                {Many:_} => rule.repeat_many_sep(sep, kind).finish(cx),
                {More:_} => rule.repeat_more_sep(sep, kind).finish(cx),
            })
        },
        {Repeat:{ repeat }} => {
            let repeat = repeat;
            handle!(match repeat {
                {Many:_} => rule.repeat_many().finish(cx),
                {More:_} => rule.repeat_more().finish(cx),
            })
        }
    })
}

fn lower_sep_kind(this: Handle<'_, '_, '_>) -> rule::SepKind {
    handle!(match this {
        {Simple:_} => rule::SepKind::Simple,
        {Trailing:_} => rule::SepKind::Trailing,
    })
}

fn lower_pattern(this: Handle<'_, '_, '_>) -> SPat {
    fn unescape(handle: Handle<'_, '_, '_>) -> String {
        let mut out = String::new();
        let s = match handle.source() {
            [FlatToken::Literal(lit)] => lit.to_string(),
            _ => unreachable!(),
        };
        let mut chars = s[1..s.len() - 1].chars();
        while let Some(c) = chars.next() {
            let c = match c {
                '\\' => match chars.next().unwrap() {
                    't' => '\t',
                    'n' => '\n',
                    'r' => '\r',
                    c => c,
                },
                _ => c,
            };
            out.push(c);
        }
        out
    }
    let unescape_char = |c| unescape(c).parse::<char>().unwrap();
    handle!(match this {
        {Str:s} => SPat::from(unescape(s)),
        {CharRange:_} => SPat::from((
            handle!(match this { {CharRange:{ start }} => Some(start), _ => None })
                .map(unescape_char)
                .map_or(Bound::Unbounded, Bound::Included),
            handle!(match this { {CharRange:{ end }} => Some(end), _ => None })
                .map(unescape_char)
                .map_or(Bound::Unbounded, Bound::Excluded),
        )),
        {CharRangeInclusive:{ end }} => SPat::from((
            handle!(match this { {CharRangeInclusive:{ start }} => Some(start), _ => None })
                .map(unescape_char)
                .map_or(Bound::Unbounded, Bound::Included),
            Bound::Included(unescape_char(end)),
        )),
    })
}
