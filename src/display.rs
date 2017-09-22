//! This module uses unsafe code because `()` does not implement `Display`,
//! which makes it impossible to hide it nicely.

use *;

use std::fmt::{Display, Formatter, Result};
use std::any::TypeId;

/// Use same layout as `Display` to allow transmuting `&TrickDisplay` into `&Display`.
/// This trait's methods will be called instead.
pub trait TrickDisplay {
    fn fmt(&self, fmt: &mut Formatter) -> Result;
}

impl TrickDisplay for () {
    fn fmt(&self, fmt: &mut Formatter) -> Result {write!(fmt, "true_1")}
}

impl<T: Display, U: Display> TrickDisplay for (T, U) {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        self.0.fmt(fmt)?;
        write!(fmt, ", ")?;
        self.1.fmt(fmt)
    }
}

macro_rules! trick_impl {
    ($a:ident, $b:tt) => {
        impl<I: TrickDisplay + 'static> TrickDisplay for $a<I> {
            fn fmt(&self, fmt: &mut Formatter) -> Result {
                <Self as Display>::fmt(self, fmt)
            }
        }

        impl<I: TrickDisplay + 'static> Display for $a<I> {
            fn fmt(&self, fmt: &mut Formatter) -> Result {
                if TypeId::of::<()>() == TypeId::of::<I>() {
                    write!(fmt, $b)?;
                } else {
                    use std::mem::transmute;
                    let i = unsafe {transmute::<&TrickDisplay, &Display>(&self.i as &TrickDisplay)};
                    write!(fmt, concat!($b, "{{{}}}"), i)?;
                }
                Ok(())
            }
        }
    };
    ($a:ident t, $b:tt) => {
        impl<T, I: TrickDisplay + 'static> TrickDisplay for $a<T, I> {
            fn fmt(&self, fmt: &mut Formatter) -> Result {
                <Self as Display>::fmt(self, fmt)
            }
        }

        impl<T, I: TrickDisplay + 'static> Display for $a<T, I> {
            fn fmt(&self, fmt: &mut Formatter) -> Result {
                if TypeId::of::<()>() == TypeId::of::<I>() {
                    write!(fmt, $b)?;
                } else {
                    use std::mem::transmute;
                    let i = unsafe {transmute::<&TrickDisplay, &Display>(&self.i as &TrickDisplay)};
                    write!(fmt, concat!($b, "{{{}}}"), i)?;
                }
                Ok(())
            }
        }
    };
    ($a:ident k, $b:tt) => {
        impl<T: Display, I: TrickDisplay + 'static> TrickDisplay for $a<T, I> {
            fn fmt(&self, fmt: &mut Formatter) -> Result {
                <Self as Display>::fmt(self, fmt)
            }
        }

        impl<T: Display, I: TrickDisplay + 'static> Display for $a<T, I> {
            fn fmt(&self, fmt: &mut Formatter) -> Result {
                if TypeId::of::<()>() == TypeId::of::<I>() {
                    write!(fmt, $b, self.k)
                } else {
                    use std::mem::transmute;
                    let i = unsafe {transmute::<&TrickDisplay, &Display>(&self.i as &TrickDisplay)};
                    write!(fmt, concat!($b, "{{{}}}"), self.k, i)
                }
            }
        }
    };
}

impl<T: Display, Co: TrickDisplay, Tr: TrickDisplay, Fa: TrickDisplay, I: 'static + TrickDisplay>
Display for IfK<T, Co, Tr, Fa, I> {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        use std::mem::transmute;
        let co = unsafe {transmute::<&TrickDisplay, &Display>(&self.co)};
        let tr = unsafe {transmute::<&TrickDisplay, &Display>(&self.tr)};
        let fa = unsafe {transmute::<&TrickDisplay, &Display>(&self.fa)};
        if TypeId::of::<()>() == TypeId::of::<I>() {
            write!(fmt, "if {}({}) {{{}}} else {{{}}}", co, self.k, tr, fa)
        } else {
            let i = unsafe {transmute::<&TrickDisplay, &Display>(&self.i)};
            write!(fmt, "if {}({}) {{{}{{{}}}}} else {{{}{{{}}}}}", co, self.k, tr, i, fa, i)
        }
    }
}

impl<Co: TrickDisplay, Tr: TrickDisplay, Fa: TrickDisplay, I: 'static + TrickDisplay>
TrickDisplay for If<Co, Tr, Fa, I> {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        <Self as Display>::fmt(self, fmt)
    }
}

impl<Co: TrickDisplay, Tr: TrickDisplay, Fa: TrickDisplay, I: 'static + TrickDisplay>
Display for If<Co, Tr, Fa, I> {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        use std::mem::transmute;
        let co = unsafe {transmute::<&TrickDisplay, &Display>(&self.co)};
        let tr = unsafe {transmute::<&TrickDisplay, &Display>(&self.tr)};
        let fa = unsafe {transmute::<&TrickDisplay, &Display>(&self.fa)};
        if TypeId::of::<()>() == TypeId::of::<I>() {
            write!(fmt, "if({}, {}, {})", co, tr, fa)
        } else {
            let i = unsafe {transmute::<&TrickDisplay, &Display>(&self.i)};
            write!(fmt, "if({}, {}, {}){{{}}}", co, tr, fa, i)
        }
    }
}

trick_impl!{LtK k, "(< {})"}
trick_impl!{EqK k, "(= {})"}
trick_impl!{GeK k, "(>= {})"}
trick_impl!{AddK k, "add({})"}
trick_impl!{Even t, "even"}
trick_impl!{Odd t, "odd"}
trick_impl!{False1 t, "false_1"}
trick_impl!{Eq t, "eq"}
trick_impl!{Add t, "add"}
trick_impl!{Id t, "id"}
trick_impl!{Not, "not"}
trick_impl!{And, "and"}
trick_impl!{Or, "or"}
trick_impl!{Xor, "xor"}
trick_impl!{Nor, "nor"}
trick_impl!{Nand, "nand"}
trick_impl!{Exc, "exc"}
trick_impl!{Nrexc, "nrexc"}
trick_impl!{Rexc, "rexc"}
trick_impl!{Nexc, "nexc"}
