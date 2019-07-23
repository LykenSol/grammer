use crate::rule::Rule;
use elsa::FrozenVec;
use std::cell::RefCell;
use std::collections::HashMap;
use std::convert::TryInto;
use std::hash::Hash;
use std::rc::Rc;

/// Context object with global resources for working with grammar,
/// such as interners.
pub struct Context<Pat> {
    interners: Interners<Pat>,
}

/// Dispatch helper, to allow implementing interning logic on
/// the type passed to `cx.intern(...)`.
pub trait InternInCx<Pat> {
    type Interned;

    fn intern_in_cx(self, cx: &mut Context<Pat>) -> Self::Interned;
}

impl<Pat: Eq + Hash> Context<Pat> {
    pub fn new() -> Self {
        Context {
            interners: Interners::default(),
        }
    }

    pub fn intern<T: InternInCx<Pat>>(&mut self, x: T) -> T::Interned {
        x.intern_in_cx(self)
    }
}

struct Interner<T: ?Sized> {
    // FIXME(Manishearth/elsa#6) switch to `FrozenIndexSet` when available.
    map: RefCell<HashMap<Rc<T>, u32>>,
    vec: FrozenVec<Rc<T>>,
}

impl<T: ?Sized + Eq + Hash> Default for Interner<T> {
    fn default() -> Self {
        Interner {
            map: RefCell::new(HashMap::default()),
            vec: FrozenVec::new(),
        }
    }
}

impl<T: ?Sized + Eq + Hash> Interner<T> {
    fn intern(&self, value: impl AsRef<T> + Into<Rc<T>>) -> u32 {
        if let Some(&i) = self.map.borrow().get(value.as_ref()) {
            return i;
        }
        let value = value.into();
        let next = self.vec.len().try_into().unwrap();
        self.map.borrow_mut().insert(value.clone(), next);
        self.vec.push(value);
        next
    }
}

macro_rules! interners {
    ($($name:ident => $ty:ty),* $(,)?) => {
        #[allow(non_snake_case)]
        struct Interners<Pat> {
            $($name: Interner<$ty>),*
        }

        impl<Pat: Eq + Hash> Default for Interners<Pat> {
            fn default() -> Self {
                Interners {
                    $($name: Default::default()),*
                }
            }
        }

        $(
            #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
            pub struct $name(u32);

            impl<Pat> std::ops::Index<$name> for Context<Pat> {
                type Output = $ty;

                fn index(&self, interned: $name) -> &Self::Output {
                    &self.interners.$name.vec[interned.0 as usize]
                }
            }
        )*
    };
}

interners! {
    IStr => str,
    IRule => Rule<Pat>,
}

impl<Pat> InternInCx<Pat> for &'_ str {
    type Interned = IStr;

    fn intern_in_cx(self, cx: &mut Context<Pat>) -> IStr {
        IStr(cx.interners.IStr.intern(self))
    }
}

// FIXME(eddyb) automate this away somehow.
impl<Pat> AsRef<Self> for Rule<Pat> {
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<Pat: Eq + Hash> InternInCx<Pat> for Rule<Pat> {
    type Interned = IRule;

    fn intern_in_cx(self, cx: &mut Context<Pat>) -> Self::Interned {
        IRule(cx.interners.IRule.intern(self))
    }
}
