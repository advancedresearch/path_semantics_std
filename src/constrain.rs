use *;

/// Implemented by higher order representations of constrained functions.
pub trait Constrain<I> {
    type Lift;

    /// Override input constraint even when existential path does not exist.
    fn i_force(&self, I) -> Self::Lift;

    /// Constrains input but only if an existential path is supported for the constraint.
    fn i(&self, i: I) -> Self::Lift where Self::Lift: ExPath {self.i_force(i)}
}

impl<I> Constrain<I> for () {
    type Lift = ();
    fn i_force(&self, _: I) -> () {()}
}

impl<Co: Clone, Tr: Clone, Fa: Clone, I, I2> Constrain<I> for If<Co, Tr, Fa, I2> {
    type Lift = If<Co, Tr, Fa, I>;
    fn i_force(&self, i: I) -> Self::Lift {
        If {co: self.co.clone(), tr: self.tr.clone(), fa: self.fa.clone(), i}
    }
}

macro_rules! con_impl {
    ($a:ident t) => {
        impl<T, I, I2> Constrain<I2> for $a<T, I> {
            type Lift = $a<T, I2>;
            fn i_force(&self, i: I2) -> Self::Lift {$a {t: PhantomData, i}}
        }
    };
    ($a:ident k) => {
        impl<T: Clone, I, I2> Constrain<I2> for $a<T, I> {
            type Lift = $a<T, I2>;
            fn i_force(&self, i: I2) -> Self::Lift {$a {k: self.k.clone(), i}}
        }
    };
    ($a:ident) => {
        impl<I, I2> Constrain<I2> for $a<I> {
            type Lift = $a<I2>;
            fn i_force(&self, i: I2) -> Self::Lift {$a {i}}
        }
    }
}

con_impl!{Not}
con_impl!{Id t}
con_impl!{False1 t}
con_impl!{And}
con_impl!{Or}
con_impl!{Eq t}
con_impl!{Xor}
con_impl!{Nand}
con_impl!{Nor}
con_impl!{Exc}
con_impl!{Rexc}
con_impl!{Nexc}
con_impl!{Nrexc}
con_impl!{Even t}
con_impl!{Odd t}
con_impl!{Add t}
con_impl!{AddK k}
con_impl!{GeK k}
con_impl!{LtK k}
con_impl!{EqK k}
