use crate::high::{type_lambda, ExistsL, PairL};
use crate::input::{Input, Range};
use indexing::{self, Container};
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::io::{self, Write};
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

pub struct Node<'i, G: GrammarReflector> {
    pub kind: G::NodeKind,
    pub range: Range<'i>,
}

// FIXME(eddyb) can't derive these on `Node<G>` because that puts bounds on `G`.
impl<G: GrammarReflector> Copy for Node<'_, G> {}
impl<G: GrammarReflector> Clone for Node<'_, G> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<G: GrammarReflector> PartialEq for Node<'_, G> {
    fn eq(&self, other: &Self) -> bool {
        (self.kind, self.range) == (other.kind, other.range)
    }
}
impl<G: GrammarReflector> Eq for Node<'_, G> {}
impl<G: GrammarReflector> PartialOrd for Node<'_, G>
where
    G::NodeKind: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (self.kind, self.range).partial_cmp(&(other.kind, other.range))
    }
}
impl<G: GrammarReflector> Ord for Node<'_, G>
where
    G::NodeKind: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        (self.kind, self.range).cmp(&(other.kind, other.range))
    }
}
impl<G: GrammarReflector> Hash for Node<'_, G> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.kind, self.range).hash(state);
    }
}

impl<G: GrammarReflector> fmt::Debug for Node<'_, G> {
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
pub struct ParseForest<'i, G: GrammarReflector, I: Input> {
    pub grammar: G,
    // HACK(eddyb) `pub(crate)` only for `parser`.
    pub(crate) input: Container<'i, I::Container>,
    pub(crate) possibilities: HashMap<Node<'i, G>, BTreeSet<usize>>,
}

type_lambda! {
    pub type<'i> ParseForestL<G: GrammarReflector, I: Input> = ParseForest<'i, G, I>;
    pub type<'i> NodeL<G: GrammarReflector> = Node<'i, G>;
}

pub type OwnedParseForestAndNode<G, I> = ExistsL<PairL<ParseForestL<G, I>, NodeL<G>>>;

#[derive(Debug)]
pub struct MoreThanOne;

impl<'i, G: GrammarReflector, I: Input> ParseForest<'i, G, I> {
    pub fn input(&self, range: Range<'i>) -> &I::Slice {
        I::slice(&self.input, range)
    }

    pub fn source_info(&self, range: Range<'i>) -> I::SourceInfo {
        I::source_info(&self.input, range)
    }

    // NOTE(eddyb) this is a private helper and should never be exported.
    fn choice_child(&self, node: Node<'i, G>, choice: usize) -> Node<'i, G> {
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

    pub fn one_choice(&self, node: Node<'i, G>) -> Result<Node<'i, G>, MoreThanOne> {
        let choices = &self.possibilities[&node];
        if choices.len() > 1 {
            return Err(MoreThanOne);
        }
        let &choice = choices.iter().next().unwrap();
        Ok(self.choice_child(node, choice))
    }

    pub fn all_choices<'a>(
        &'a self,
        node: Node<'i, G>,
    ) -> impl Iterator<Item = Node<'i, G>> + Clone + 'a
    where
        G::NodeKind: 'a,
    {
        self.possibilities[&node]
            .iter()
            .cloned()
            .map(move |choice| self.choice_child(node, choice))
    }

    // NOTE(eddyb) this is a private helper and should never be exported.
    fn split_children(&self, node: Node<'i, G>, split: usize) -> (Node<'i, G>, Node<'i, G>) {
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

    pub fn one_split(&self, node: Node<'i, G>) -> Result<(Node<'i, G>, Node<'i, G>), MoreThanOne> {
        let splits = &self.possibilities[&node];
        if splits.len() > 1 {
            return Err(MoreThanOne);
        }
        let &split = splits.iter().next().unwrap();
        Ok(self.split_children(node, split))
    }

    pub fn all_splits<'a>(
        &'a self,
        node: Node<'i, G>,
    ) -> impl Iterator<Item = (Node<'i, G>, Node<'i, G>)> + Clone + 'a
    where
        G::NodeKind: 'a,
    {
        self.possibilities[&node]
            .iter()
            .cloned()
            .map(move |split| self.split_children(node, split))
    }

    pub fn unpack_alias(&self, node: Node<'i, G>) -> Node<'i, G> {
        match self.grammar.node_shape(node.kind) {
            NodeShape::Alias(inner) => Node {
                kind: inner,
                range: node.range,
            },
            shape => unreachable!("unpack_alias({:?}): non-alias shape {:?}", node, shape),
        }
    }

    pub fn unpack_opt(&self, node: Node<'i, G>) -> Option<Node<'i, G>> {
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
            let mut add_children = |children: &[(&str, Node<'i, G>)]| -> io::Result<()> {
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

// FIXME(rust-lang/rust#54175) work around iterator adapter compile-time
// blowup issues by using a makeshift "non-determinism arrow toolkit".
pub mod nd {
    use std::iter;
    use std::marker::PhantomData;

    pub trait Arrow: Copy {
        type Input;
        type Output;
        type Iter: Iterator<Item = Self::Output> + Clone;
        fn apply(&self, x: Self::Input) -> Self::Iter;

        fn map<F: Fn(Self::Output) -> R, R>(self, f: F) -> Map<Self, F> {
            Map(self, f)
        }
        fn then<B: Arrow<Input = Self::Output>>(self, b: B) -> Then<Self, B> {
            Then(self, b)
        }
        fn pairs<B: Arrow>(self, b: B) -> Pairs<Self, B>
        where
            Self::Output: Copy,
            B::Input: Copy,
        {
            Pairs(self, b)
        }
    }

    macro_rules! derive_copy {
        ($name:ident<$($param:ident $(: $bound:ident)*),*>) => {
            impl<$($param $(: $bound)*),*> Copy for $name<$($param),*> {}
            impl<$($param $(: $bound)*),*> Clone for $name<$($param),*> {
                fn clone(&self) -> Self {
                    *self
                }
            }
        }
    }

    pub struct Id<T>(PhantomData<T>);
    derive_copy!(Id<T>);
    impl<T> Id<T> {
        pub fn new() -> Self {
            Id(PhantomData)
        }
    }
    impl<T: Clone> Arrow for Id<T> {
        type Input = T;
        type Output = T;
        type Iter = iter::Once<T>;
        fn apply(&self, x: T) -> Self::Iter {
            iter::once(x)
        }
    }

    pub struct FromIter<T, F>(F, PhantomData<T>);
    derive_copy!(FromIter<T, F: Copy>);
    impl<T, F> FromIter<T, F> {
        pub fn new(f: F) -> Self {
            FromIter(f, PhantomData)
        }
    }
    impl<T, F: Copy + Fn(T) -> I, I: Iterator + Clone> Arrow for FromIter<T, F> {
        type Input = T;
        type Output = I::Item;
        type Iter = I;
        fn apply(&self, x: T) -> I {
            self.0(x)
        }
    }

    pub struct FromIterK<K, T, F>(K, F, PhantomData<T>);
    derive_copy!(FromIterK<K: Copy, T, F: Copy>);
    impl<K, T, F> FromIterK<K, T, F> {
        pub fn new(k: K, f: F) -> Self {
            FromIterK(k, f, PhantomData)
        }
    }
    impl<K: Copy, T, F: Copy + Fn(K, T) -> I, I: Iterator + Clone> Arrow for FromIterK<K, T, F> {
        type Input = T;
        type Output = I::Item;
        type Iter = I;
        fn apply(&self, x: T) -> I {
            self.1(self.0, x)
        }
    }

    #[derive(Copy, Clone)]
    pub struct Map<A, F>(A, F);
    impl<A: Arrow, F: Copy + Fn(A::Output) -> R, R> Arrow for Map<A, F> {
        type Input = A::Input;
        type Output = R;
        type Iter = iter::Map<A::Iter, F>;
        fn apply(&self, x: Self::Input) -> Self::Iter {
            self.0.apply(x).map(self.1)
        }
    }

    #[derive(Clone)]
    pub struct ThenIter<A: Arrow, B: Arrow<Input = A::Output>> {
        a_iter: A::Iter,
        b_arrow: B,
        b_iter: Option<B::Iter>,
        // HACK(eddyb) this field is useless (never set to `Some`)
        // (see `match self.b_iter_backwards` below for more details).
        b_iter_backwards: Option<B::Iter>,
    }
    impl<A: Arrow, B: Arrow<Input = A::Output>> Iterator for ThenIter<A, B> {
        type Item = B::Output;
        fn next(&mut self) -> Option<Self::Item> {
            loop {
                if let Some(ref mut b_iter) = self.b_iter {
                    if let x @ Some(_) = b_iter.next() {
                        return x;
                    }
                }
                match self.a_iter.next() {
                    // HACK(eddyb) this never does anything, but without a *second*
                    // call to `B::Iter::next`, LLVM spends more time optimizing.
                    None => {
                        return match self.b_iter_backwards {
                            Some(ref mut b_iter) => b_iter.next(),
                            None => None,
                        }
                    }
                    Some(x) => self.b_iter = Some(self.b_arrow.apply(x)),
                }
            }
        }
    }

    #[derive(Copy, Clone)]
    pub struct Then<A, B>(A, B);
    impl<A: Arrow, B: Arrow<Input = A::Output>> Arrow for Then<A, B> {
        type Input = A::Input;
        type Output = B::Output;
        type Iter = ThenIter<A, B>;
        fn apply(&self, x: Self::Input) -> Self::Iter {
            ThenIter {
                a_iter: self.0.apply(x),
                b_arrow: self.1,
                b_iter: None,
                b_iter_backwards: None,
            }
        }
    }

    #[derive(Clone)]
    pub struct PairsIter<A: Arrow, B: Arrow>
    where
        A::Output: Copy,
        B::Input: Copy,
    {
        a_iter: A::Iter,
        b_iter0: B::Iter,
        a_output_b_iter: Option<(A::Output, B::Iter)>,
    }
    impl<A: Arrow, B: Arrow> Iterator for PairsIter<A, B>
    where
        A::Output: Copy,
        B::Input: Copy,
    {
        type Item = (A::Output, B::Output);
        fn next(&mut self) -> Option<Self::Item> {
            loop {
                if let Some((x, ref mut b_iter)) = self.a_output_b_iter {
                    if let Some(y) = b_iter.next() {
                        return Some((x, y));
                    }
                }
                match self.a_iter.next() {
                    None => return None,
                    Some(x) => {
                        self.a_output_b_iter = Some((x, self.b_iter0.clone()));
                    }
                }
            }
        }
    }

    #[derive(Copy, Clone)]
    pub struct Pairs<A, B>(A, B);
    impl<A: Arrow, B: Arrow> Arrow for Pairs<A, B>
    where
        A::Output: Copy,
        B::Input: Copy,
    {
        type Input = (A::Input, B::Input);
        type Output = (A::Output, B::Output);
        type Iter = PairsIter<A, B>;
        fn apply(&self, (x, y): Self::Input) -> Self::Iter {
            PairsIter {
                a_iter: self.0.apply(x),
                b_iter0: self.1.apply(y),
                a_output_b_iter: None,
            }
        }
    }
}

// HACK(eddyb) work around `macro_rules` not being `use`-able.
pub use crate::__forest_traverse as traverse;

#[macro_export]
macro_rules! __forest_traverse {
    (typeof($leaf:ty) _) => { $leaf };
    (typeof($leaf:ty) ?) => { Option<traverse!(typeof($leaf) _)> };
    (typeof($leaf:ty) ($l_shape:tt, $r_shape:tt)) => { (traverse!(typeof($leaf) $l_shape), traverse!(typeof($leaf) $r_shape)) };
    (typeof($leaf:ty) { $($i:tt $_i:ident: $kind:pat => $shape:tt,)* }) => { ($(traverse!(typeof($leaf) $shape),)*) };
    (typeof($leaf:ty) [$shape:tt]) => { (traverse!(typeof($leaf) $shape),) };

    (one($forest:ident, $node:ident) _) => {
        $node
    };
    (one($forest:ident, $node:ident) ?) => {
        Some($node)
    };
    (one($forest:ident, $node:ident) ($l_shape:tt, $r_shape:tt)) => {
        {
            let (left, right) = $forest.one_split($node)?;
            (
                traverse!(one($forest, left) $l_shape),
                traverse!(one($forest, right) $r_shape),
            )
        }
    };
    (one($forest:ident, $node:ident) { $($i:tt $_i:ident: $kind:pat => $shape:tt,)* }) => {
        {
            let node = $forest.one_choice($node)?;
            let mut r = <($(traverse!(typeof(_) $shape),)*)>::default();
            match node.kind {
                $($kind => r.$i = traverse!(one($forest, node) $shape),)*
                _ => unreachable!(),
            }
            r
        }
    };
    (one($forest:ident, $node:ident) [$shape:tt]) => {
        {
            let mut r = <(traverse!(typeof(_) $shape),)>::default();
            if let Some(node) = $forest.unpack_opt($node) {
                r.0 = traverse!(one($forest, node) $shape);
            }
            r
        }
    };

    (all($forest:ident) _) => {
        $crate::forest::nd::Id::new()
    };
    (all($forest:ident) ?) => {
        $crate::forest::nd::Id::new().map(Some)
    };
    (all($forest:ident) ($l_shape:tt, $r_shape:tt)) => {
        $crate::forest::nd::FromIterK::new($forest, $crate::forest::ParseForest::all_splits)
            .then(traverse!(all($forest) $l_shape).pairs(traverse!(all($forest) $r_shape)))
    };
    (all($forest:ident) { $($i:tt $_i:ident: $kind:pat => $shape:tt,)* }) => {
        $crate::forest::nd::FromIter::new(move |node| {
            #[derive(Clone)]
            enum Iter<$($_i),*> {
                $($_i($_i)),*
            }
            impl<$($_i: Iterator),*> Iterator for Iter<$($_i),*>
                where $($_i::Item: Default),*
            {
                type Item = ($($_i::Item),*);
                fn next(&mut self) -> Option<Self::Item> {
                    let mut r = Self::Item::default();
                    match self {
                        $(Iter::$_i(iter) => r.$i = iter.next()?),*
                    }
                    Some(r)
                }
            }
            $forest.all_choices(node).flat_map(move |node| {
                match node.kind {
                    $($kind => Iter::$_i(traverse!(all($forest) $shape).apply(node)),)*
                    _ => unreachable!(),
                }
            })
        })
    };
    (all($forest:ident) [$shape:tt]) => {
        $crate::forest::nd::FromIter::new(move |node| {
            match $forest.unpack_opt(node) {
                Some(node) => {
                    Some(traverse!(all($forest) $shape).apply(node).map(|x| (x,)))
                        .into_iter().flatten().chain(None)
                }
                None => {
                    None.into_iter().flatten().chain(Some(<_>::default()))
                }
            }
        })
    }
}
