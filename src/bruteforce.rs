use crate::context::{Context, IRule, IStr};
use crate::forest::{
    dynamic::{CxAndGrammar, OwnedHandle},
    Node,
};
use crate::input::{Input, InputMatch, Range};
use crate::parser::{ParseResult, Parser};
use crate::rule::{Rule, SepKind};
use cyclotron::bruteforce;
use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::{BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::Hash;
use std::iter;
use std::ops::{RangeFrom, RangeTo};
use std::rc::Rc;

#[derive(Clone, Default, Debug)]
struct CachedParse {
    lengths: Rc<BTreeSet<usize>>,
    approx_forest: Rc<ApproxForest>,
}

// HACK(eddyb) hide `approx_forest` from the cyclotron, no need to
// ensure a fixpoint for it (and `HashMap` could make that tricky).
impl PartialEq for CachedParse {
    fn eq(&self, other: &Self) -> bool {
        self.lengths == other.lengths
    }
}

impl Eq for CachedParse {}

/// An approximation of a parse forest, erasing the end of ranges
/// wherever convenient, to minimize allocations (especially for lists,
/// where this is linear instead of quadratic).
///
/// NB: Requires a second validation pass to produce a proper SPPF.
#[derive(Default, Debug)]
struct ApproxForest {
    possibilities: HashMap<(IRule, RangeFrom<usize>), (Option<RangeTo<usize>>, SmallSet<usize>)>,
}

#[derive(Debug)]
enum SmallSet<T> {
    One(T),
    Many(BTreeSet<T>),
}

impl<T: Copy + Ord> SmallSet<T> {
    fn insert(&mut self, value: T) {
        match self {
            SmallSet::One(prev) => {
                if value != *prev {
                    *self = SmallSet::Many([*prev, value].iter().cloned().collect());
                }
            }
            SmallSet::Many(set) => {
                set.insert(value);
            }
        }
    }

    fn iter<'a>(&'a self) -> impl Iterator<Item = &'a T> {
        match self {
            SmallSet::One(x) => Some(x).into_iter().chain(None.into_iter().flatten()),
            SmallSet::Many(set) => None
                .into_iter()
                .chain(Some(set.iter()).into_iter().flatten()),
        }
    }
}

impl ApproxForest {
    fn add(&mut self, rule: IRule, start: RangeFrom<usize>, end: Option<RangeTo<usize>>, x: usize) {
        use std::collections::hash_map::Entry;

        match self.possibilities.entry((rule, start)) {
            Entry::Vacant(entry) => {
                entry.insert((end, SmallSet::One(x)));
            }
            Entry::Occupied(entry) => {
                let (old_end, set) = entry.into_mut();
                if end != *old_end {
                    *old_end = None;
                }
                set.insert(x);
            }
        }
    }
}

fn parse_inner<'i, Pat: Clone + Ord + Hash + fmt::Debug, I: Input>(
    // FIXME(eddyb) group some of these in a `struct`.
    cx: &Context<Pat>,
    grammar: &crate::Grammar,
    parser: &RefCell<Parser<'_, 'i, CxAndGrammar<'_, Pat>, I, Pat>>,
    parse_cached: &mut dyn FnMut((IRule, Range<'i>)) -> CachedParse,
    approx_forest: &mut ApproxForest,
    rule: IRule,
    range: Range<'i>,
) -> BTreeSet<usize>
where
    I::Slice: InputMatch<Pat>,
{
    match cx[rule] {
        Rule::Empty => iter::once(0).collect(),
        // FIXME(eddyb) find a way to avoid cloning the pattern.
        Rule::Eat(ref pat) => parser
            .borrow_mut()
            .with_result_and_remaining(Range(range.frontiers().0), range)
            .input_consume_left(pat.clone())
            .map(|parser| parser.result().len())
            .into_iter()
            .collect(),
        // FIXME(eddyb) avoid cloning the set from behind a `Rc`.
        // May require something like `Cow` but for `T | Rc<T>`?
        Rule::Call(r) => (*parse_cached((grammar.rules[&r].rule, range)).lengths).clone(),
        Rule::Concat([left, right]) => {
            let mut lengths = BTreeSet::new();

            for left_len in parse_inner(
                cx,
                grammar,
                parser,
                parse_cached,
                approx_forest,
                left,
                range,
            ) {
                let (_, after_left, _) = range.split_at(left_len);
                for right_len in parse_inner(
                    cx,
                    grammar,
                    parser,
                    parse_cached,
                    approx_forest,
                    right,
                    Range(after_left),
                ) {
                    let len = left_len + right_len;

                    approx_forest.add(rule, range.start().., Some(..range.start() + len), left_len);

                    lengths.insert(len);
                }
            }

            lengths
        }
        Rule::Or(ref cases) => {
            let mut lengths = BTreeSet::new();

            for (i, &case) in cases.iter().enumerate() {
                for len in parse_inner(
                    cx,
                    grammar,
                    parser,
                    parse_cached,
                    approx_forest,
                    case,
                    range,
                ) {
                    approx_forest.add(rule, range.start().., Some(..range.start() + len), i);

                    lengths.insert(len);
                }
            }

            lengths
        }
        Rule::Opt(rule) => iter::once(0)
            .chain(parse_inner(
                cx,
                grammar,
                parser,
                parse_cached,
                approx_forest,
                rule,
                range,
            ))
            .collect(),
        Rule::RepeatMany(..) => parse_inner(
            cx,
            grammar,
            parser,
            parse_cached,
            approx_forest,
            rule.expand_repeats(cx),
            range,
        ),
        Rule::RepeatMore(elem, sep) => {
            let concat_elem_tail_rule = rule.expand_repeats(cx);
            // FIXME(eddyb) dedup this with `IRule::expand_repeats`.
            let sep = sep.map(|(sep, kind)| {
                (
                    sep,
                    kind,
                    cx.intern(Rule::Concat([
                        sep,
                        match kind {
                            SepKind::Simple => rule,
                            SepKind::Trailing => {
                                cx.intern(Rule::RepeatMany(elem, Some((sep, SepKind::Trailing))))
                            }
                        },
                    ])),
                )
            });

            let mut lengths = BTreeSet::new();

            // To avoid using stack space linear in the list length,
            // and time/heap space quadratic in the list length,
            // this uses a min-heap (`BinaryHeap` + `ord::Reverse`)
            // as a queue, in a monotonic loop, completing a previous
            // list with one more element (if possible) at every step.
            let mut starts = BinaryHeap::new();
            starts.push(Reverse(0));
            while let Some(Reverse(start)) = starts.pop() {
                let range = Range(range.split_at(start).1);
                for elem_len in parse_inner(
                    cx,
                    grammar,
                    parser,
                    parse_cached,
                    approx_forest,
                    elem,
                    range,
                ) {
                    approx_forest.add(concat_elem_tail_rule, range.start().., None, elem_len);

                    let after_elem = Range(range.split_at(elem_len).1);
                    let end = start + elem_len;
                    if !lengths.insert(end) {
                        // Seen this list before, avoid re-enqueing it.
                        continue;
                    }

                    if let Some((sep, kind, concat_sep_tail_rule)) = sep {
                        for sep_len in parse_inner(
                            cx,
                            grammar,
                            parser,
                            parse_cached,
                            approx_forest,
                            sep,
                            after_elem,
                        ) {
                            starts.push(Reverse(end + sep_len));
                            approx_forest.add(
                                concat_sep_tail_rule,
                                after_elem.start()..,
                                None,
                                sep_len,
                            );

                            match kind {
                                SepKind::Simple => {}
                                SepKind::Trailing => {
                                    // The list can also end after the
                                    // separator, not only before.
                                    lengths.insert(end + sep_len);
                                }
                            }
                        }
                    } else {
                        starts.push(Reverse(end));
                    }
                }
            }

            lengths
        }
    }
}

fn build_sppf<'a, 'i, Pat: Clone + Ord + Hash + fmt::Debug, I: Input>(
    cx: &Context<Pat>,
    grammar: &crate::Grammar,
    parser: &RefCell<Parser<'_, 'i, CxAndGrammar<'a, Pat>, I, Pat>>,
    mut parse_cached: impl FnMut((IRule, Range<'i>)) -> CachedParse,
    root: Node<'i, CxAndGrammar<'a, Pat>>,
) where
    I::Slice: InputMatch<Pat>,
{
    let full_input = parser.borrow().remaining();

    // Unpack `rule`, knowing it matched `range`, into a simpler
    // rule, if possible. Only returns `None` for leaves.
    let trivial_unpack_valid = |mut rule, range: Range<'_>| {
        loop {
            match cx[rule] {
                    Rule::Empty | Rule::Eat(_) => return None,

                    Rule::Opt(child) => if range.is_empty() {
                        return None;
                    } else {
                        rule = child;
                    }

                    Rule::RepeatMany(..) |
                    // FIXME(eddyb) handling `RepeatMore` is a waste of time.
                    // Maybe remove once repeats aren't aliases anymore?
                    Rule::RepeatMore(..) => rule = rule.expand_repeats(cx),

                    _ => return Some(rule),
                }
        }
    };

    // Build the SPPF starting with "roots" known to be valid, and descending
    // into their children. Only descendants of ambiguous nodes need validation,
    // everything else can be assumed valid and inserted into the SPPF directly.
    let mut roots = VecDeque::new();
    let mut seen_roots = HashSet::new();
    let mut valid_cache = HashMap::new();
    let mut stack = vec![];

    roots.push_back((<Rc<ApproxForest>>::default(), root.kind, root.range));
    seen_roots.insert((root.kind, root.range));

    'roots: while let Some((approx_forest, mut rule, mut range)) = roots.pop_front() {
        let mut add_root = |approx_forest: &Rc<_>, rule, range| {
            if let Some(rule) = trivial_unpack_valid(rule, range) {
                if seen_roots.insert((rule, range)) {
                    roots.push_back((Rc::clone(approx_forest), rule, range));
                }
            }
        };

        // Peel off as many unambiguous layers of rules as possible.
        loop {
            let old = valid_cache.insert((rule, range), true);
            if let Some(old) = old {
                assert!(old);
                continue 'roots;
            }

            let possibilities = || {
                let (end, set) = &approx_forest.possibilities[&(rule, range.start()..)];
                if let Some(end) = end {
                    assert_eq!(*end, ..range.end());
                }
                let mut possibilities = set.iter().cloned();
                (possibilities.next().unwrap(), possibilities.next())
            };

            match cx[rule] {
                // Handled by `trivial_unpack_valid`.
                Rule::Empty
                | Rule::Eat(_)
                | Rule::Opt(_)
                | Rule::RepeatMany(..)
                | Rule::RepeatMore(..) => unreachable!(),

                Rule::Call(r) => {
                    let rule = grammar.rules[&r].rule;
                    let result = parse_cached((rule, Range(full_input.split_at(range.start()).1)));
                    assert!(result.lengths.contains(&range.len()));
                    add_root(&result.approx_forest, rule, range);
                    continue 'roots;
                }

                Rule::Concat([left, right]) => {
                    let (split, second_split) = possibilities();
                    assert!(split <= range.len());

                    // Only ambiguous if the second possibility also fits in this range.
                    if second_split.filter(|&x| x <= range.len()).is_some() {
                        break;
                    }

                    let (left_range, right_range, _) = range.split_at(split);

                    add_root(&approx_forest, left, Range(left_range));

                    // HACK(eddyb) need a more ergonomic SPPF builder/parser API.
                    parser
                        .borrow_mut()
                        .with_result_and_remaining(
                            Range(right_range),
                            Range(full_input.split_at(range.end()).1),
                        )
                        .forest_add_split(
                            rule,
                            Node {
                                kind: left,
                                range: Range(left_range),
                            },
                        );

                    rule = right;
                    range = Range(right_range);
                }

                Rule::Or(ref cases) => {
                    let (choice, second_choice) = possibilities();
                    if second_choice.is_some() {
                        break;
                    }

                    // HACK(eddyb) need a more ergonomic SPPF builder/parser API.
                    parser
                        .borrow_mut()
                        .with_result_and_remaining(range, Range(full_input.split_at(range.end()).1))
                        .forest_add_choice(rule, choice);

                    rule = cases[choice];
                }
            }
            rule = match trivial_unpack_valid(rule, range) {
                Some(rule) => rule,
                None => continue 'roots,
            };
        }

        // If we reach this point, we have ambiguities that we need to validate
        // recursively. To avoid running out of stack, we use an emulated one.
        stack.clear();
        stack.push((
            rule,
            range,
            // FIXME(eddyb) reduce the cost of this (already computed above).
            approx_forest.possibilities[&(rule, range.start()..)]
                .1
                .iter()
                .cloned()
                .next()
                .unwrap(),
            false,
        ));

        'stack: while let Some(&(rule, range, i, _any_valid)) = stack.last() {
            let (mut rule, range) = match cx[rule] {
                Rule::Concat([_, right]) => (right, Range(range.split_at(i).1)),

                Rule::Or(ref cases) => (cases[i], range),

                // Only `Concat` and `Or` can be on the stack.
                _ => unreachable!(),
            };

            // Try to unpack the `Concat`/`Or` child - note that this only
            // exits directly when a leaf is reached, while reaching
            // `Concat`/`Or` results in `continue 'stack`.
            let mut valid = loop {
                let first_possibility = || {
                    let (end, set) = approx_forest.possibilities.get(&(rule, range.start()..))?;
                    if let Some(end) = end {
                        if *end != ..range.end() {
                            return None;
                        }
                    }
                    set.iter().cloned().next()
                };

                if let Some(&valid) = valid_cache.get(&(rule, range)) {
                    break valid;
                }

                let valid = match cx[rule] {
                    Rule::Empty => range.is_empty(),

                    // FIXME(eddyb) maybe checking the pattern again would be cheaper?
                    Rule::Eat(_) => {
                        parse_cached((rule, Range(full_input.split_at(range.start()).1)))
                            .lengths
                            .contains(&range.len())
                    }

                    Rule::Call(r) => {
                        let rule = grammar.rules[&r].rule;
                        let result =
                            parse_cached((rule, Range(full_input.split_at(range.start()).1)));
                        let valid = result.lengths.contains(&range.len());
                        if valid {
                            add_root(&result.approx_forest, rule, range);
                        }
                        valid
                    }

                    Rule::Concat(_) => match first_possibility().filter(|&x| x <= range.len()) {
                        Some(split) => {
                            stack.push((rule, range, split, false));
                            continue 'stack;
                        }
                        None => false,
                    },

                    Rule::Or(_) => match first_possibility() {
                        Some(choice) => {
                            stack.push((rule, range, choice, false));
                            continue 'stack;
                        }
                        None => false,
                    },

                    Rule::Opt(child) => {
                        if range.is_empty() {
                            true
                        } else {
                            rule = child;
                            continue;
                        }
                    }

                    Rule::RepeatMany(..) | Rule::RepeatMore(..) => {
                        rule = rule.expand_repeats(cx);
                        continue;
                    }
                };

                valid_cache.insert((rule, range), valid);
                break valid;
            };

            // Commit the validity into the parent frames, advance them to
            // the next split/choice, and pop them if they're complete.
            while let Some(&mut (rule, range, ref mut i, ref mut any_valid)) = stack.last_mut() {
                if valid {
                    *any_valid = true;

                    // FIXME(eddyb) deduplicate this with the other place which
                    // does exactly this.
                    match cx[rule] {
                        Rule::Concat([left, _]) => {
                            let split = *i;

                            let (left_range, right_range, _) = range.split_at(split);

                            add_root(&approx_forest, left, Range(left_range));

                            // HACK(eddyb) need a more ergonomic SPPF builder/parser API.
                            parser
                                .borrow_mut()
                                .with_result_and_remaining(
                                    Range(right_range),
                                    Range(full_input.split_at(range.end()).1),
                                )
                                .forest_add_split(
                                    rule,
                                    Node {
                                        kind: left,
                                        range: Range(left_range),
                                    },
                                );
                        }

                        Rule::Or(_) => {
                            let choice = *i;

                            // HACK(eddyb) need a more ergonomic SPPF builder/parser API.
                            parser
                                .borrow_mut()
                                .with_result_and_remaining(
                                    range,
                                    Range(full_input.split_at(range.end()).1),
                                )
                                .forest_add_choice(rule, choice);
                        }

                        // Only `Concat` and `Or` can be on the stack.
                        _ => unreachable!(),
                    }
                }

                // Try to advance this frame.
                let mut next = match &approx_forest.possibilities[&(rule, range.start()..)].1 {
                    SmallSet::One(_) => None,
                    SmallSet::Many(set) => {
                        use std::ops::Bound::*;
                        set.range((Excluded(*i), Unbounded)).next().cloned()
                    }
                };
                if let Rule::Concat(_) = cx[rule] {
                    next = next.filter(|&x| x <= range.len());
                }

                match next {
                    Some(next) => {
                        // Advance this frame and keep it around.
                        *i = next;
                        continue 'stack;
                    }
                    None => {
                        // Pop this frame and repeat for its parent frame.
                        valid = *any_valid;
                        valid_cache.insert((rule, range), valid);
                        stack.pop();
                    }
                }
            }
        }
    }
}

pub fn parse<'a, Pat: Clone + Ord + Hash + fmt::Debug, I: Input>(
    cx: &'a Context<Pat>,
    grammar: &'a crate::Grammar,
    named_rule: IStr,
    input: I,
) -> ParseResult<I::SourceInfoPoint, Pat, OwnedHandle<'a, Pat, I>>
where
    I::Slice: InputMatch<Pat>,
{
    Parser::parse_with(CxAndGrammar { cx, grammar }, input, |parser| {
        let full_input = parser.remaining();
        let parser = &RefCell::new(parser);
        let mut parse_cached = bruteforce::memoize(|parse_cached, (rule, range)| {
            let mut approx_forest = ApproxForest::default();
            let lengths = parse_inner(
                cx,
                grammar,
                parser,
                parse_cached,
                &mut approx_forest,
                rule,
                range,
            );
            CachedParse {
                lengths: Rc::new(lengths),
                approx_forest: Rc::new(approx_forest),
            }
        });

        let longest = parse_cached((grammar.rules[&named_rule].rule, full_input))
            .lengths
            .iter()
            .cloned()
            .rev()
            .next()?;
        let node = Node {
            kind: cx.intern(Rule::Call(named_rule)),
            range: Range(full_input.split_at(longest).0),
        };

        // Only construct the SPPF in case of success.
        if node.range == full_input {
            build_sppf(cx, grammar, parser, parse_cached, node);
        }

        Some(node)
    })
    .map(|forest_and_node| OwnedHandle { forest_and_node })
}
