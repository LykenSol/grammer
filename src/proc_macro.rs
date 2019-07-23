use crate::rule::{call, eat, MatchesEmpty, MaybeKnown};
use crate::scannerless::Pat as SPat;
pub use proc_macro2::{
    Delimiter, Ident, LexError, Literal, Punct, Spacing, Span, TokenStream, TokenTree,
};
use std::fmt;
use std::ops::Deref;
use std::str::FromStr;

pub type Context = crate::context::Context<Pat>;

pub fn builtin(cx: &mut Context) -> crate::Grammar {
    let mut g = crate::Grammar::new();

    let ident = eat(Pat(vec![FlatTokenPat::Ident(None)])).finish(cx);
    g.define(cx.intern("IDENT"), ident.clone());

    g.define(
        cx.intern("LIFETIME"),
        eat(Pat(vec![
            FlatTokenPat::Punct {
                ch: Some('\''),
                joint: Some(true),
            },
            FlatTokenPat::Ident(None),
        ]))
        .finish(cx),
    );

    let punct = eat(Pat(vec![FlatTokenPat::Punct {
        ch: None,
        joint: None,
    }]))
    .finish(cx);
    g.define(cx.intern("PUNCT"), punct.clone());

    let literal = eat(Pat(vec![FlatTokenPat::Literal])).finish(cx);
    g.define(cx.intern("LITERAL"), literal.clone());

    let delim = |c| eat(FlatTokenPat::Delim(c));
    let group = |open, close| delim(open) + call("TOKEN_TREE").repeat_many() + delim(close);
    g.define(
        cx.intern("TOKEN_TREE"),
        (ident | punct | literal | group('(', ')') | group('[', ']') | group('{', '}')).finish(cx),
    );

    g
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pat<Pats = Vec<FlatTokenPat<String>>>(pub Pats);

impl FromStr for Pat {
    type Err = LexError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Handle lone delimiters first, as they won't lex.
        let mut chars = s.chars();
        if let (Some(ch), None) = (chars.next(), chars.next()) {
            if "()[]{}".contains(ch) {
                return Ok(FlatTokenPat::Delim(ch).into());
            }
        }

        let mut tokens = vec![];
        flatten(s.parse()?, &mut tokens);
        Ok(Pat(tokens.into_iter().map(|tt| tt.extract_pat()).collect()))
    }
}

// FIXME(eddyb) perhaps support `TryFrom`/`TryInto` directly in `grammar_grammar`?
impl From<&str> for Pat {
    fn from(s: &str) -> Self {
        s.parse().unwrap()
    }
}

impl<Pats> From<Pats> for Pat<Pats> {
    fn from(pats: Pats) -> Self {
        Pat(pats)
    }
}

impl From<FlatTokenPat<String>> for Pat {
    fn from(pat: FlatTokenPat<String>) -> Self {
        Pat(vec![pat])
    }
}

impl From<SPat> for Pat {
    fn from(pat: SPat) -> Self {
        match pat {
            SPat::String(s) => s[..].into(),
            SPat::Range(..) => unimplemented!("char ranges are unsupported"),
        }
    }
}

impl MatchesEmpty for Pat {
    fn matches_empty(&self) -> MaybeKnown<bool> {
        MaybeKnown::Known(self.0.is_empty())
    }
}

pub enum FlatToken {
    Delim(char, Span),
    Ident(Ident),
    Punct(Punct),
    Literal(Literal),
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FlatTokenPat<S: AsRef<str>> {
    Delim(char),
    Ident(Option<S>),
    Punct {
        ch: Option<char>,
        joint: Option<bool>,
    },
    Literal,
}

impl<S: AsRef<str>> fmt::Debug for FlatTokenPat<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FlatTokenPat::Delim(c) | FlatTokenPat::Punct { ch: Some(c), .. } => {
                write!(f, "\"{}\"", c)
            }
            FlatTokenPat::Ident(None) => f.write_str("IDENT"),
            FlatTokenPat::Ident(Some(ident)) => write!(f, "\"{}\"", ident.as_ref()),
            FlatTokenPat::Punct { ch: None, .. } => f.write_str("PUNCT"),
            FlatTokenPat::Literal => f.write_str("LITERAL"),
        }
    }
}

// FIXME(eddyb) can't use `Pats: AsRef<[FlatTokenPat<S>]` as it doesn't constrain `S`.
impl<S: AsRef<str>, Pats: Deref<Target = [FlatTokenPat<S>]>> fmt::Debug for Pat<Pats> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0[..] {
            [] => f.write_str("\"\""),
            [pat] => pat.fmt(f),
            pats => {
                let mut was_joint = true;
                f.write_str("\"")?;
                for pat in pats {
                    if !was_joint {
                        f.write_str(" ")?;
                    }
                    match pat {
                        FlatTokenPat::Punct { ch: Some(c), joint } => {
                            write!(f, "{}", c)?;
                            was_joint = *joint == Some(true);
                        }
                        FlatTokenPat::Ident(Some(ident)) => {
                            write!(f, "\"{}\"", ident.as_ref())?;
                            was_joint = false;
                        }
                        _ => unreachable!(),
                    }
                }
                f.write_str("\"")
            }
        }
    }
}

impl FlatToken {
    pub fn span(&self) -> Span {
        match self {
            &FlatToken::Delim(_, span) => span,
            FlatToken::Ident(tt) => tt.span(),
            FlatToken::Punct(tt) => tt.span(),
            FlatToken::Literal(tt) => tt.span(),
        }
    }

    pub fn extract_pat(&self) -> FlatTokenPat<String> {
        match self {
            &FlatToken::Delim(delim, _) => FlatTokenPat::Delim(delim),
            FlatToken::Ident(tt) => FlatTokenPat::Ident(Some(tt.to_string())),
            FlatToken::Punct(tt) => FlatTokenPat::Punct {
                ch: Some(tt.as_char()),
                joint: if tt.spacing() == Spacing::Joint {
                    Some(true)
                } else {
                    None
                },
            },
            FlatToken::Literal(tt) => {
                unimplemented!(
                    "matching specific literals is not supported, \
                     use `LITERAL` instead of `{}`",
                    tt.to_string(),
                );
            }
        }
    }

    pub fn matches_pat(&self, pat: &FlatTokenPat<impl AsRef<str>>) -> bool {
        match (self, pat) {
            (FlatToken::Delim(a, _), FlatTokenPat::Delim(b)) => a == b,
            (FlatToken::Ident(_), FlatTokenPat::Ident(None)) => true,
            (FlatToken::Ident(a), FlatTokenPat::Ident(Some(b))) => a == b.as_ref(),
            (FlatToken::Punct(a), FlatTokenPat::Punct { ch, joint }) => {
                ch.map_or(true, |b| a.as_char() == b)
                    && joint.map_or(true, |b| (a.spacing() == Spacing::Joint) == b)
            }
            (FlatToken::Literal(_), FlatTokenPat::Literal) => true,
            _ => false,
        }
    }
}

pub(crate) fn flatten(stream: TokenStream, out: &mut Vec<FlatToken>) {
    for tt in stream {
        let flat = match tt {
            TokenTree::Group(tt) => {
                let delim = tt.delimiter();
                // FIXME(eddyb) use proper delim span here.
                let span = tt.span();
                let stream = tt.stream();
                let (open, close) = match delim {
                    Delimiter::Parenthesis => ('(', ')'),
                    Delimiter::Brace => ('{', '}'),
                    Delimiter::Bracket => ('[', ']'),
                    Delimiter::None => {
                        // FIXME(eddyb) maybe encode implicit delimiters somehow?
                        // One way could be to have an opaque `FlatToken` variant,
                        // containing the entire group, instead of exposing its contents.
                        flatten(stream, out);
                        continue;
                    }
                };
                out.push(FlatToken::Delim(open, span));
                flatten(stream, out);
                FlatToken::Delim(close, span)
            }
            TokenTree::Ident(tt) => FlatToken::Ident(tt),
            TokenTree::Punct(tt) => FlatToken::Punct(tt),
            TokenTree::Literal(tt) => FlatToken::Literal(tt),
        };
        out.push(flat);
    }
}
