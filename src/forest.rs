use crate::input::Input;
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::io::{self, Write};
use std::ops::Range;
use std::str;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum NodeShape<T> {
    Opaque,
    Alias(T),
    Choice(usize),
    Opt(T),
    Split(T, T),
}

impl<T: fmt::Display> fmt::Display for NodeShape<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeShape::Opaque => write!(f, "Opaque"),
            NodeShape::Alias(inner) => write!(f, "Alias({})", inner),
            NodeShape::Choice(count) => write!(f, "Choice({})", count),
            NodeShape::Opt(inner) => write!(f, "Opt({})", inner),
            NodeShape::Split(left, right) => write!(f, "Split({}, {})", left, right),
        }
    }
}

impl<T> NodeShape<T> {
    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> NodeShape<U> {
        match self {
            NodeShape::Opaque => NodeShape::Opaque,
            NodeShape::Alias(inner) => NodeShape::Alias(f(inner)),
            NodeShape::Choice(count) => NodeShape::Choice(count),
            NodeShape::Opt(inner) => NodeShape::Opt(f(inner)),
            NodeShape::Split(left, right) => NodeShape::Split(f(left), f(right)),
        }
    }
}

/// Objects capable of providing information about various parts of the grammar
/// (mostly parse nodes and their substructure).
///
/// For code generation, this doesn't need to be more than an unit struct, as
/// all the information can be hardcoded, but in more dynamic settings, this
/// might contain e.g. a reference to a context.
pub trait GrammarReflector {
    type NodeKind: fmt::Debug + Eq + Hash + Copy;

    fn node_shape(&self, kind: Self::NodeKind) -> NodeShape<Self::NodeKind>;
    fn node_shape_choice_get(&self, kind: Self::NodeKind, i: usize) -> Self::NodeKind;
    fn node_desc(&self, kind: Self::NodeKind) -> String;
}

pub struct Node<G: GrammarReflector> {
    pub kind: G::NodeKind,
    pub range: std::ops::Range<usize>,
}

// FIXME(eddyb) can't derive these on `Node<G>` because that puts bounds on `G`.
impl<G: GrammarReflector> Copy for Node<G> {}
impl<G: GrammarReflector> Clone for Node<G> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<G: GrammarReflector> PartialEq for Node<G> {
    fn eq(&self, other: &Self) -> bool {
        (self.kind, self.range) == (other.kind, other.range)
    }
}
impl<G: GrammarReflector> Eq for Node<G> {}
impl<G: GrammarReflector> PartialOrd for Node<G>
where
    G::NodeKind: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self.kind, self.range).partial_cmp(&(other.kind, other.range))
    }
}
impl<G: GrammarReflector> Ord for Node<G>
where
    G::NodeKind: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        (self.kind, self.range).cmp(&(other.kind, other.range))
    }
}
impl<G: GrammarReflector> Hash for Node<G> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.kind, self.range).hash(state);
    }
}

impl<G: GrammarReflector> fmt::Debug for Node<G> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?} @ {}..{}",
            self.kind,
            self.range.start(),
            self.range.end()
        )
    }
}

/// A parse forest, in SPPF (Shared Packed Parse Forest) representation.
pub struct ParseForest<G: GrammarReflector, I: Input> {
    pub grammar: G,
    // HACK(eddyb) `pub(crate)` only for `parser`.
    pub(crate) input: I::Container,
    pub(crate) possibilities: HashMap<Node<G>, BTreeSet<usize>>,
}

#[derive(Debug)]
pub struct MoreThanOne;

impl<G: GrammarReflector, I: Input> ParseForest<G, I> {
    pub fn input(&self, range: Range<usize>) -> &I::Slice {
        I::slice(&self.input, range)
    }

    pub fn source_info(&self, range: Range<usize>) -> I::SourceInfo {
        I::source_info(&self.input, range)
    }

    // NOTE(eddyb) this is a private helper and should never be exported.
    fn choice_child(&self, node: Node<G>, choice: usize) -> Node<G> {
        match self.grammar.node_shape(node.kind) {
            NodeShape::Choice(_) => Node {
                kind: self.grammar.node_shape_choice_get(node.kind, choice),
                range: node.range,
            },
            shape => unreachable!(
                "choice_child({:?}, {}): non-choice shape {:?}",
                node, choice, shape
            ),
        }
    }

    pub fn one_choice(&self, node: Node<G>) -> Result<Node<G>, MoreThanOne> {
        let choices = &self.possibilities[&node];
        if choices.len() > 1 {
            return Err(MoreThanOne);
        }
        let &choice = choices.iter().next().unwrap();
        Ok(self.choice_child(node, choice))
    }

    pub fn all_choices<'a>(&'a self, node: Node<G>) -> impl Iterator<Item = Node<G>> + Clone + 'a
    where
        G::NodeKind: 'a,
    {
        self.possibilities[&node]
            .iter()
            .cloned()
            .map(move |choice| self.choice_child(node, choice))
    }

    // NOTE(eddyb) this is a private helper and should never be exported.
    fn split_children(&self, node: Node<G>, split: usize) -> (Node<G>, Node<G>) {
        match self.grammar.node_shape(node.kind) {
            NodeShape::Split(left_kind, right_kind) => {
                let (left, right, _) = node.range.split_at(split);
                (
                    Node {
                        kind: left_kind,
                        range: Range(left),
                    },
                    Node {
                        kind: right_kind,
                        range: Range(right),
                    },
                )
            }
            shape => unreachable!(
                "split_children({:?}, {}): non-split shape {:?}",
                node, split, shape
            ),
        }
    }

    pub fn one_split(&self, node: Node<G>) -> Result<(Node<G>, Node<G>), MoreThanOne> {
        let splits = &self.possibilities[&node];
        if splits.len() > 1 {
            return Err(MoreThanOne);
        }
        let &split = splits.iter().next().unwrap();
        Ok(self.split_children(node, split))
    }

    pub fn all_splits<'a>(
        &'a self,
        node: Node<G>,
    ) -> impl Iterator<Item = (Node<G>, Node<G>)> + Clone + 'a
    where
        G::NodeKind: 'a,
    {
        self.possibilities[&node]
            .iter()
            .cloned()
            .map(move |split| self.split_children(node, split))
    }

    pub fn unpack_alias(&self, node: Node<G>) -> Node<G> {
        match self.grammar.node_shape(node.kind) {
            NodeShape::Alias(inner) => Node {
                kind: inner,
                range: node.range,
            },
            shape => unreachable!("unpack_alias({:?}): non-alias shape {:?}", node, shape),
        }
    }

    pub fn unpack_opt(&self, node: Node<G>) -> Option<Node<G>> {
        match self.grammar.node_shape(node.kind) {
            NodeShape::Opt(inner) => {
                if node.range.is_empty() {
                    None
                } else {
                    Some(Node {
                        kind: inner,
                        range: node.range,
                    })
                }
            }
            shape => unreachable!("unpack_opt({:?}): non-opt shape {:?}", node, shape),
        }
    }

    pub fn dump_graphviz(&self, out: &mut dyn Write) -> io::Result<()> {
        writeln!(out, "digraph forest {{")?;
        let mut queue: VecDeque<_> = self.possibilities.keys().cloned().collect();
        let mut seen: HashSet<_> = queue.iter().cloned().collect();
        let mut p = 0;
        let node_name = |Node { kind, range }| {
            format!(
                "{} @ {:?}",
                self.grammar.node_desc(kind),
                self.source_info(range)
            )
        };
        while let Some(source) = queue.pop_front() {
            let source_name = node_name(source);
            writeln!(out, "    {:?} [shape=box]", source_name)?;
            let mut add_children = |children: &[(&str, Node<G>)]| -> io::Result<()> {
                writeln!(out, r#"    p{} [label="" shape=point]"#, p)?;
                writeln!(out, "    {:?} -> p{}:n", source_name, p)?;
                for &(port, child) in children {
                    writeln!(
                        out,
                        "    p{}:{} -> {:?}:n [dir=none]",
                        p,
                        port,
                        node_name(child)
                    )?;
                    if seen.insert(child) {
                        queue.push_back(child);
                    }
                }
                p += 1;
                Ok(())
            };
            match self.grammar.node_shape(source.kind) {
                NodeShape::Opaque => {}

                NodeShape::Alias(_) => {
                    add_children(&[("s", self.unpack_alias(source))])?;
                }

                NodeShape::Opt(_) => {
                    if let Some(child) = self.unpack_opt(source) {
                        add_children(&[("s", child)])?;
                    }
                }

                NodeShape::Choice(_) => {
                    for child in self.all_choices(source) {
                        add_children(&[("s", child)])?;
                    }
                }

                NodeShape::Split(..) => {
                    for (left, right) in self.all_splits(source) {
                        add_children(&[("sw", left), ("se", right)])?;
                    }
                }
            }
        }
        writeln!(out, "}}")
    }
}

pub mod typed {
    use super::{GrammarReflector, MoreThanOne, Node, ParseForest};
    use crate::input::Input;

    #[derive(Clone)]
    enum Void {}

    // HACK(eddyb) this type uses `T` but is also uninhabited.
    type PhantomVoid<T> = (Void, std::marker::PhantomData<T>);

    pub trait Shaped {
        type Shape: Shape;

        // FIXME(eddyb) this is always `[usize; Self::Shape::STATE_LEN]`.
        // (but that doesn't work yet)
        type State: Default + AsMut<[usize]>;
    }

    pub trait FromShapeFields<'a, G: GrammarReflector, I: Input>: Sized {
        type Output;

        // FIXME(eddyb) use an array length const here instead when that works.
        type Fields: Default + AsMut<[Option<Node<G>>]>;

        fn from_shape_fields(forest: &'a ParseForest<G, I>, fields: Self::Fields) -> Self::Output;

        fn one(forest: &'a ParseForest<G, I>, node: Node<G>) -> Result<Self::Output, MoreThanOne>
        where
            Self: Shaped,
        {
            let mut state = Self::State::default();
            let state = state.as_mut();
            assert_eq!(state.len(), Self::Shape::STATE_LEN);

            Self::Shape::init(forest, node, state);

            let mut fields = Self::Fields::default();
            Self::Shape::read(forest, node, state, fields.as_mut());

            if Self::Shape::step(forest, node, state) {
                Err(MoreThanOne)
            } else {
                Ok(Self::from_shape_fields(forest, fields))
            }
        }

        fn all(forest: &'a ParseForest<G, I>, node: Node<G>) -> ShapedAllIter<'a, G, I, Self>
        where
            Self: Shaped,
        {
            let mut state = Self::State::default();
            assert_eq!(state.as_mut().len(), Self::Shape::STATE_LEN);

            Self::Shape::init(forest, node, state.as_mut());

            ShapedAllIter {
                forest,
                node,
                state: Some(state),
            }
        }
    }

    pub struct ShapedAllIter<'a, G: GrammarReflector, I: Input, T: Shaped> {
        forest: &'a ParseForest<G, I>,
        node: Node<G>,
        state: Option<T::State>,
    }

    impl<'a, G: GrammarReflector, I: Input, T: Shaped> Iterator for ShapedAllIter<'a, G, I, T>
    where
        T: FromShapeFields<'a, G, I>,
    {
        type Item = T::Output;

        fn next(&mut self) -> Option<T::Output> {
            let state = self.state.as_mut()?.as_mut();
            let mut fields = T::Fields::default();
            T::Shape::read(self.forest, self.node, state, fields.as_mut());
            if !T::Shape::step(self.forest, self.node, state) {
                self.state.take();
            }
            Some(T::from_shape_fields(self.forest, fields))
        }
    }

    impl Shaped for () {
        type Shape = shape!(_);
        type State = [usize; <shape!(_)>::STATE_LEN];
    }

    impl<G: GrammarReflector, I: Input> FromShapeFields<'_, G, I> for () {
        type Output = ();
        type Fields = [Option<Node<G>>; 0];

        fn from_shape_fields(_: &ParseForest<G, I>, []: Self::Fields) {}
    }

    impl<'a, G: GrammarReflector, I: Input, T> FromShapeFields<'a, G, I> for Option<T>
    where
        T: FromShapeFields<'a, G, I, Fields = [Option<Node<G>>; 1]>,
    {
        type Output = Option<T::Output>;
        type Fields = [Option<Node<G>>; 1];

        fn from_shape_fields(
            forest: &'a ParseForest<G, I>,
            [node]: Self::Fields,
        ) -> Option<T::Output> {
            Some(T::from_shape_fields(forest, [Some(node?)]))
        }
    }

    pub struct WithShape<T, A: Shape, S: Default + AsMut<[usize]>>(PhantomVoid<(T, A, S)>);

    impl<T, A: Shape, S: Default + AsMut<[usize]>> Shaped for WithShape<T, A, S> {
        type Shape = A;
        type State = S;
    }

    impl<'a, G: GrammarReflector, I: Input, T, A, S> FromShapeFields<'a, G, I> for WithShape<T, A, S>
    where
        T: FromShapeFields<'a, G, I>,
        A: Shape,
        S: Default + AsMut<[usize]>,
    {
        type Output = T::Output;
        type Fields = T::Fields;

        fn from_shape_fields(forest: &'a ParseForest<G, I>, fields: T::Fields) -> T::Output {
            T::from_shape_fields(forest, fields)
        }
    }

    pub trait Shape {
        const STATE_LEN: usize;

        fn init<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &mut [usize],
        );
        fn read<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &[usize],
            fields: &mut [Option<Node<G>>],
        );
        fn step<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &mut [usize],
        ) -> bool;
    }

    pub struct Leaf(PhantomVoid<()>);

    impl Shape for Leaf {
        const STATE_LEN: usize = 0;

        fn init<G: GrammarReflector, I: Input>(_: &ParseForest<G, I>, _: Node<G>, _: &mut [usize]) {
        }
        fn read<G: GrammarReflector, I: Input>(
            _: &ParseForest<G, I>,
            _: Node<G>,
            _: &[usize],
            _: &mut [Option<Node<G>>],
        ) {
        }
        fn step<G: GrammarReflector, I: Input>(
            _: &ParseForest<G, I>,
            _: Node<G>,
            _: &mut [usize],
        ) -> bool {
            false
        }
    }

    // FIXME(eddyb) this should be using const generics.
    pub struct Field<X: Default + AsRef<[()]>>(PhantomVoid<X>);

    impl<X: Default + AsRef<[()]>> Shape for Field<X> {
        const STATE_LEN: usize = 0;

        fn init<G: GrammarReflector, I: Input>(_: &ParseForest<G, I>, _: Node<G>, _: &mut [usize]) {
        }
        fn read<G: GrammarReflector, I: Input>(
            _: &ParseForest<G, I>,
            node: Node<G>,
            _: &[usize],
            fields: &mut [Option<Node<G>>],
        ) {
            fields[X::default().as_ref().len()] = Some(node);
        }
        fn step<G: GrammarReflector, I: Input>(
            _: &ParseForest<G, I>,
            _: Node<G>,
            _: &mut [usize],
        ) -> bool {
            false
        }
    }

    pub struct Split<Left: Shape, Right: Shape>(PhantomVoid<(Left, Right)>);

    impl<Left: Shape, Right: Shape> Shape for Split<Left, Right> {
        const STATE_LEN: usize = 1 + Left::STATE_LEN + Right::STATE_LEN;

        fn init<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &mut [usize],
        ) {
            let (state_split, state) = state.split_at_mut(1);
            let state_split = &mut state_split[0];
            let (state_left, state_right) = state.split_at_mut(Left::STATE_LEN);

            let &split = forest.possibilities[&node].iter().next().unwrap();

            let (left, right) = forest.split_children(node, split);

            *state_split = split;
            Left::init(forest, left, state_left);
            Right::init(forest, right, state_right);
        }
        fn read<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &[usize],
            fields: &mut [Option<Node<G>>],
        ) {
            let (state_split, state) = state.split_at(1);
            let state_split = state_split[0];
            let (state_left, state_right) = state.split_at(Left::STATE_LEN);

            let (left, right) = forest.split_children(node, state_split);
            Left::read(forest, left, state_left, fields);
            Right::read(forest, right, state_right, fields);
        }
        fn step<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &mut [usize],
        ) -> bool {
            let (state_split, state) = state.split_at_mut(1);
            let state_split = &mut state_split[0];
            let (state_left, state_right) = state.split_at_mut(Left::STATE_LEN);

            let (left, right) = forest.split_children(node, *state_split);

            Right::step(forest, right, state_right)
                || Left::step(forest, left, state_left) && {
                    Right::init(forest, right, state_right);
                    true
                }
                || ({
                    use std::ops::Bound::*;
                    forest.possibilities[&node]
                        .range((Excluded(*state_split), Unbounded))
                        .next()
                        .cloned()
                })
                .map(|split| {
                    *state_split = split;

                    let (left, right) = forest.split_children(node, split);

                    Left::init(forest, left, state_left);
                    Right::init(forest, right, state_right);
                })
                .is_some()
        }
    }

    pub struct Choice<At: Shape, Cases: Shape>(PhantomVoid<(At, Cases)>);

    impl<At: Shape, Cases: Shape> Shape for Choice<At, Cases> {
        const STATE_LEN: usize = At::STATE_LEN + Cases::STATE_LEN;

        fn init<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &mut [usize],
        ) {
            let (state_at, state_cases) = state.split_at_mut(At::STATE_LEN);

            let &choice = forest.possibilities[&node].iter().next().unwrap();

            let child = forest.choice_child(node, choice);

            state_cases[0] = choice;
            At::init(forest, child, state_at);
            Cases::init(forest, child, state_cases);
        }
        fn read<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &[usize],
            fields: &mut [Option<Node<G>>],
        ) {
            let (state_at, state_cases) = state.split_at(At::STATE_LEN);

            let child = forest.choice_child(node, state_cases[0]);

            At::read(forest, child, state_at, fields);
            Cases::read(forest, child, state_cases, fields);
        }
        fn step<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &mut [usize],
        ) -> bool {
            let (state_at, state_cases) = state.split_at_mut(At::STATE_LEN);

            let child = forest.choice_child(node, state_cases[0]);

            At::step(forest, child, state_at)
                || Cases::step(forest, child, state_cases) && {
                    At::init(forest, child, state_at);
                    true
                }
                || ({
                    use std::ops::Bound::*;
                    forest.possibilities[&node]
                        .range((Excluded(state_cases[0]), Unbounded))
                        .next()
                        .cloned()
                })
                .map(|choice| {
                    state_cases[0] = choice;

                    let child = forest.choice_child(node, choice);

                    At::init(forest, child, state_at);
                    Cases::init(forest, child, state_cases);
                })
                .is_some()
        }
    }

    pub trait CaseList: Shape {
        const LEN: usize;
    }

    pub struct CaseAppend<Prefix: CaseList, Last: Shape>(PhantomVoid<(Prefix, Last)>);

    impl<Prefix: CaseList, Last: Shape> CaseList for CaseAppend<Prefix, Last> {
        const LEN: usize = Prefix::LEN + 1;
    }

    impl<Prefix: CaseList, Last: Shape> Shape for CaseAppend<Prefix, Last> {
        const STATE_LEN: usize = {
            // HACK(eddyb) this is just `max(1 + Last::STATE_LEN, Prefix::STATE_LEN)`.
            let a = 1 + Last::STATE_LEN;
            let b = Prefix::STATE_LEN;

            let a_gt_b_mask = -((a > b) as isize) as usize;
            (a_gt_b_mask & a) | (!a_gt_b_mask & b)
        };

        fn init<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &mut [usize],
        ) {
            let (state_choice, state_last) = state.split_at_mut(1);
            let state_choice = state_choice[0];

            if state_choice != Prefix::LEN {
                Prefix::init(forest, node, state);
            } else {
                Last::init(forest, node, state_last);
            }
        }
        fn read<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &[usize],
            fields: &mut [Option<Node<G>>],
        ) {
            let (state_choice, state_last) = state.split_at(1);
            let state_choice = state_choice[0];

            if state_choice != Prefix::LEN {
                Prefix::read(forest, node, state, fields);
            } else {
                Last::read(forest, node, state_last, fields);
            }
        }
        fn step<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &mut [usize],
        ) -> bool {
            let (state_choice, state_last) = state.split_at_mut(1);
            let state_choice = state_choice[0];

            if state_choice != Prefix::LEN {
                Prefix::step(forest, node, state)
            } else {
                Last::step(forest, node, state_last)
            }
        }
    }

    pub struct CaseEmpty(PhantomVoid<()>);

    impl CaseList for CaseEmpty {
        const LEN: usize = 0;
    }

    impl Shape for CaseEmpty {
        const STATE_LEN: usize = 0;

        fn init<G: GrammarReflector, I: Input>(_: &ParseForest<G, I>, _: Node<G>, _: &mut [usize]) {
            unreachable!()
        }
        fn read<G: GrammarReflector, I: Input>(
            _: &ParseForest<G, I>,
            _: Node<G>,
            _: &[usize],
            _: &mut [Option<Node<G>>],
        ) {
            unreachable!()
        }
        fn step<G: GrammarReflector, I: Input>(
            _: &ParseForest<G, I>,
            _: Node<G>,
            _: &mut [usize],
        ) -> bool {
            unreachable!()
        }
    }

    pub struct Opt<A: Shape>(PhantomVoid<A>);

    impl<A: Shape> Shape for Opt<A> {
        const STATE_LEN: usize = A::STATE_LEN;

        fn init<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &mut [usize],
        ) {
            if let Some(child) = forest.unpack_opt(node) {
                A::init(forest, child, state);
            }
        }
        fn read<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &[usize],
            fields: &mut [Option<Node<G>>],
        ) {
            if let Some(child) = forest.unpack_opt(node) {
                A::read(forest, child, state, fields);
            }
        }
        fn step<G: GrammarReflector, I: Input>(
            forest: &ParseForest<G, I>,
            node: Node<G>,
            state: &mut [usize],
        ) -> bool {
            match forest.unpack_opt(node) {
                Some(child) => A::step(forest, child, state),
                None => false,
            }
        }
    }

    // HACK(eddyb) work around `macro_rules` not being `use`-able.
    pub use crate::__forest_typed_shape as shape;

    #[macro_export]
    macro_rules! __forest_typed_shape {
        (_) => {
            $crate::forest::typed::Leaf
        };
        ($i:literal) => {
            $crate::forest::typed::Field<[(); $i]>
        };
        (($l_shape:tt $r_shape:tt)) => {
            $crate::forest::typed::Split<
                $crate::forest::typed::shape!($l_shape),
                $crate::forest::typed::shape!($r_shape),
            >
        };
        ({ $at_shape:tt @ $($shape:tt)* }) => {
            $crate::forest::typed::Choice<
                $crate::forest::typed::shape!($at_shape),
                $crate::forest::typed::shape!(cases { $($shape)* } rev {}),
            >
        };
        // HACK(eddyb) have to reverse the tt list to produce a "snoc-list"
        // instead of "cons-list".
        (cases { $shape0:tt $($shape:tt)* } rev { $($shape_rev:tt)* }) => {
            $crate::forest::typed::shape!(cases { $($shape)* } rev { $shape0 $($shape_rev)* })
        };
        (cases {} rev { $shape_last:tt $($shape:tt)* }) => {
            $crate::forest::typed::CaseAppend<
                $crate::forest::typed::shape!(cases {} rev { $($shape)* }),
                $crate::forest::typed::shape!($shape_last),
            >
        };
        (cases {} rev {}) => { $crate::forest::typed::CaseEmpty };
        ([$shape:tt]) => {
            $crate::forest::typed::Opt<
                $crate::forest::typed::shape!($shape),
            >
        }
    }
}
