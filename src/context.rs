use indexmap::IndexSet;
use std::convert::TryInto;
use std::marker::PhantomData;

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

impl<Pat> Context<Pat> {
    pub fn new() -> Self {
        Context {
            interners: Interners::default(),
        }
    }

    pub fn intern<T: InternInCx<Pat>>(&mut self, x: T) -> T::Interned {
        x.intern_in_cx(self)
    }
}

macro_rules! interners {
    ($($name:ident => $ty:ty),* $(,)?) => {
        #[allow(non_snake_case)]
        struct Interners<Pat> {
            $($name: IndexSet<$ty>,)*
            _marker: PhantomData<Pat>,
        }

        impl<Pat> Default for Interners<Pat> {
            fn default() -> Self {
                Interners {
                    $($name: IndexSet::new(),)*
                    _marker: PhantomData,
                }
            }
        }

        $(
            #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
            pub struct $name(u32);

            impl<Pat> InternInCx<Pat> for $ty {
                type Interned = $name;

                fn intern_in_cx(self, cx: &mut Context<Pat>) -> Self::Interned {
                    $name(cx.interners.$name.insert_full(self).0.try_into().unwrap())
                }
            }

            impl<Pat> std::ops::Index<$name> for Context<Pat> {
                type Output = $ty;

                fn index(&self, interned: $name) -> &Self::Output {
                    self.interners.$name.get_index(interned.0 as usize).unwrap()
                }
            }
        )*
    };
}

interners! {
    IStr => String,
}

impl<Pat> InternInCx<Pat> for &'_ str {
    type Interned = IStr;

    fn intern_in_cx(self, cx: &mut Context<Pat>) -> IStr {
        // Avoid allocating if this string is already in the interner.
        if let Some((i, _)) = cx.interners.IStr.get_full(self) {
            return IStr(i.try_into().unwrap());
        }

        cx.intern(self.to_string())
    }
}
