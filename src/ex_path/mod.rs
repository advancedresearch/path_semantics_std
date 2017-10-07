use *;

/// Existential path of constrained function.
pub trait ExPath {
    type Lift;

    fn ex_path(&self) -> Self::Lift;
}

impl ExPath for () {
    type Lift = Id<bool>;

    fn ex_path(&self) -> Self::Lift {Id::default()}
}

// When the same function are in both branches of an `if` expression,
// the condition is irrelevant.
impl<C, T, I: Clone> ExPath for If<C, T, T, I>
    where T: Constrain<I>, T::Lift: ExPath
{
    type Lift = <<T as Constrain<I>>::Lift as ExPath>::Lift;

    fn ex_path(&self) -> Self::Lift {
        self.tr.i(self.i.clone()).ex_path()
    }
}

// Take the existential path of the branches.
// This makes the `IfK` object map back to itself nicely.
impl<T: Clone, C: Clone, A: ExPath, B: ExPath> ExPath for IfK<T, C, A, B> {
    type Lift = IfK<T, C, A::Lift, B::Lift>;

    fn ex_path(&self) -> Self::Lift {
        IfK {
            k: self.k.clone(), co: self.co.clone(),
            tr: self.tr.ex_path(), fa: self.fa.ex_path(), i: ()
        }
    }
}

macro_rules! ex_impl {
    // Apply transformation to a tuple with two functions.
    ($a:ident < $at:ident , ( $t:ty , $u:ty ) > ) => {
        impl ExPath for $a<$at, ($t, $u)> {
            type Lift = (<$a<$at, $t> as ExPath>::Lift, <$a<$at, $u> as ExPath>::Lift);

            fn ex_path(&self) -> Self::Lift {
                (self.i_force(self.i.0).ex_path(), self.i_force(self.i.1).ex_path())
            }
        }
    };
        // Apply transformation to a tuple with two functions.
    (T $a:ident < $at:ident , ( $t:ty , $u:ty ) > ) => {
        impl<T: Clone> ExPath for $a<$at, ($t, $u)> {
            type Lift = (<$a<$at, $t> as ExPath>::Lift, <$a<$at, $u> as ExPath>::Lift);

            fn ex_path(&self) -> Self::Lift {
                (self.i_force(self.i.0.clone()).ex_path(), self.i_force(self.i.1.clone()).ex_path())
            }
        }
    };
    // Apply transformation to a tuple with two functions.
    ($a:ident < ( $t:ty , $u:ty ) > ) => {
        impl ExPath for $a<($t, $u)> {
            type Lift = (<$a<$t> as ExPath>::Lift, <$a<$u> as ExPath>::Lift);

            fn ex_path(&self) -> Self::Lift {
                (self.i_force(self.i.0).ex_path(), self.i_force(self.i.1).ex_path())
            }
        }
    };
    (T $a:ty , ()) => {
        impl<T> ExPath for $a {
            type Lift = ();

            fn ex_path(&self) -> () {()}
        }
    };
    (T $a:ty , $b:ident) => {
        impl<T> ExPath for $a {
            type Lift = $b;

            fn ex_path(&self) -> $b {$b::default()}
        }
    };
    (T $a:ty , $b:ident < $bt:ident >) => {
        impl<T> ExPath for $a {
            type Lift = $b<$bt>;

            fn ex_path(&self) -> $b<$bt> {$b::<$bt>::default()}
        }
    };
    (T U $a:ty , $b:ident) => {
        impl<T, U> ExPath for $a {
            type Lift = $b;

            fn ex_path(&self) -> $b {$b::default()}
        }
    };
    (K $a:ty , $b:ident < $bt:ident >) => {
        impl ExPath for $a {
            type Lift = $b<$bt>;

            fn ex_path(&self) -> $b<$bt> {$b {k: self.k.clone(), i: ()}}
        }
    };
    ($a:ty , $b:ident) => {
        impl ExPath for $a {
            type Lift = $b;

            fn ex_path(&self) -> $b {$b::default()}
        }
    };
    ($a:ty , $b:ident < $t:ident >) => {
        impl ExPath for $a {
            type Lift = $b<$t>;

            fn ex_path(&self) -> $b<$t> {$b::<$t>::default()}
        }
    };
    ($a:ty , ()) => {
        impl ExPath for $a {
            type Lift = ();

            fn ex_path(&self) -> () {()}
        }
    };
}

ex_impl!{Not, ()}
ex_impl!{Not<Not>, Id<bool>}
ex_impl!{Not<Id<bool>>, Not}
ex_impl!{Not<(Not, ())>}
ex_impl!{Not<((), Not)>}
ex_impl!{Not<(Not, Not)>}
ex_impl!{Not<(Not, Id<bool>)>}
ex_impl!{Not<(Id<bool>, Not)>}
ex_impl!{Not<(Id<bool>, Id<bool>)>}
ex_impl!{Not<((), ())>}
ex_impl!{T Id<T>, ()}
ex_impl!{Id<bool, Not>, Not}
ex_impl!{T U False1<T, U>, Not}
ex_impl!{And, ()}
ex_impl!{And<((), ())>}
ex_impl!{And<Not>, Not}
ex_impl!{And<Id<bool>>, Id<bool>}
ex_impl!{And<(Not, ())>, Not}
ex_impl!{And<((), Not)>, Not}
ex_impl!{And<(Not, Not)>, Not}
ex_impl!{And<(Id<bool>, ())>, ()}
ex_impl!{And<((), Id<bool>)>, ()}
ex_impl!{And<(Id<bool>, Id<bool>)>, Id<bool>}
ex_impl!{And<(Not, Id<bool>)>, Not}
ex_impl!{And<(Id<bool>, Not)>, Not}
ex_impl!{Or, ()}
ex_impl!{Or<((), ())>}
ex_impl!{Or<Not>, Not}
ex_impl!{Or<Id<bool>>, Id<bool>}
ex_impl!{Or<(Not, ())>, ()}
ex_impl!{Or<((), Not)>, ()}
ex_impl!{Or<(Not, Not)>, Not}
ex_impl!{Or<(Id<bool>, ())>, Id<bool>}
ex_impl!{Or<((), Id<bool>)>, Id<bool>}
ex_impl!{Or<(Id<bool>, Id<bool>)>, Id<bool>}
ex_impl!{Or<(Not, Id<bool>)>, Id<bool>}
ex_impl!{Or<(Id<bool>, Not)>, Id<bool>}
ex_impl!{T Eq<T>, ()}
ex_impl!{Eq<bool, ((), ())>}
ex_impl!{Eq<bool, Not>, Id<bool>}
ex_impl!{Eq<bool, Id<bool>>, Id<bool>}
ex_impl!{Eq<bool, (Not, ())>, ()}
ex_impl!{Eq<bool, ((), Not)>, ()}
ex_impl!{Eq<bool, (Not, Not)>, Id<bool>}
ex_impl!{Eq<bool, (Id<bool>, ())>, ()}
ex_impl!{Eq<bool, ((), Id<bool>)>, ()}
ex_impl!{Eq<bool, (Id<bool>, Id<bool>)>, Id<bool>}
ex_impl!{Eq<bool, (Not, Id<bool>)>, Not}
ex_impl!{Eq<bool, (Id<bool>, Not)>, Not}
ex_impl!{T EqK<T>, ()}
ex_impl!{Xor, ()}
ex_impl!{Xor<((), ())>}
ex_impl!{Xor<Id<bool>>, Not}
ex_impl!{Xor<Not>, Not}
ex_impl!{Xor<(Not, ())>, ()}
ex_impl!{Xor<((), Not)>, ()}
ex_impl!{Xor<(Not, Not)>, Not}
ex_impl!{Xor<(Id<bool>, ())>, ()}
ex_impl!{Xor<((), Id<bool>)>, ()}
ex_impl!{Xor<(Id<bool>, Id<bool>)>, Not}
ex_impl!{Xor<(Not, Id<bool>)>, Id<bool>}
ex_impl!{Xor<(Id<bool>, Not)>, Id<bool>}
ex_impl!{Nand, ()}
ex_impl!{Nand<((), ())>}
ex_impl!{Nand<Not>, Id<bool>}
ex_impl!{Nand<Id<bool>>, Not}
ex_impl!{Nand<((), Not)>, Id<bool>}
ex_impl!{Nand<(Not, ())>, Id<bool>}
ex_impl!{Nand<(Not, Not)>, Id<bool>}
ex_impl!{Nand<(Id<bool>, ())>, ()}
ex_impl!{Nand<((), Id<bool>)>, ()}
ex_impl!{Nand<(Id<bool>, Id<bool>)>, Not}
ex_impl!{Nand<(Not, Id<bool>)>, Id<bool>}
ex_impl!{Nand<(Id<bool>, Not)>, Id<bool>}
ex_impl!{Nor, ()}
ex_impl!{Nor<((), ())>, ()}
ex_impl!{Nor<Not>, Id<bool>}
ex_impl!{Nor<(Not, ())>, ()}
ex_impl!{Nor<((), Not)>, ()}
ex_impl!{Nor<(Not, Not)>, Id<bool>}
ex_impl!{Nor<(Id<bool>, ())>, Not}
ex_impl!{Nor<((), Id<bool>)>, Not}
ex_impl!{Nor<Id<bool>>, Not}
ex_impl!{Nor<(Id<bool>, Id<bool>)>, Not}
ex_impl!{Nor<(Not, Id<bool>)>, Not}
ex_impl!{Nor<(Id<bool>, Not)>, Not}
ex_impl!{Exc, ()}
ex_impl!{Exc<((), ())>, ()}
ex_impl!{Exc<Not>, Not}
ex_impl!{Exc<(Not, ())>, Not}
ex_impl!{Exc<((), Not)>, ()}
ex_impl!{Exc<(Not, Not)>, Not}
ex_impl!{Exc<(Id<bool>, ())>, ()}
ex_impl!{Exc<((), Id<bool>)>, Not}
ex_impl!{Exc<Id<bool>>, Not}
ex_impl!{Exc<(Id<bool>, Id<bool>)>, Not}
ex_impl!{Exc<(Not, Id<bool>)>, Not}
ex_impl!{Exc<(Id<bool>, Not)>, Id<bool>}
ex_impl!{Nrexc, ()}
ex_impl!{Nrexc<((), ())>, ()}
ex_impl!{Nrexc<Not>, Id<bool>}
ex_impl!{Nrexc<(Not, ())>, ()}
ex_impl!{Nrexc<((), Not)>, Id<bool>}
ex_impl!{Nrexc<(Not, Not)>, Id<bool>}
ex_impl!{Nrexc<(Id<bool>, ())>, Id<bool>}
ex_impl!{Nrexc<((), Id<bool>)>, ()}
ex_impl!{Nrexc<(Id<bool>, Id<bool>)>, Id<bool>}
ex_impl!{Nrexc<Id<bool>>, Id<bool>}
ex_impl!{Nrexc<(Not, Id<bool>)>, Not}
ex_impl!{Nrexc<(Id<bool>, Not)>, Id<bool>}
ex_impl!{Rexc, ()}
ex_impl!{Rexc<Not>, Not}
ex_impl!{Rexc<((), ())>, ()}
ex_impl!{Rexc<((), Not)>, Not}
ex_impl!{Rexc<(Not, ())>, ()}
ex_impl!{Rexc<Id<bool>>, Not}
ex_impl!{Rexc<(Id<bool>, Id<bool>)>, Not}
ex_impl!{Rexc<(Not, Not)>, Not}
ex_impl!{Rexc<((), Id<bool>)>, ()}
ex_impl!{Rexc<(Id<bool>, ())>, Not}
ex_impl!{Rexc<(Not, Id<bool>)>, Id<bool>}
ex_impl!{Rexc<(Id<bool>, Not)>, Not}
ex_impl!{Nexc, ()}
ex_impl!{Nexc<Not>, Id<bool>}
ex_impl!{Nexc<(Not, ())>, Id<bool>}
ex_impl!{Nexc<((), Not)>, ()}
ex_impl!{Nexc<((), ())>, ()}
ex_impl!{Nexc<(Not, Not)>, Id<bool>}
ex_impl!{Nexc<Id<bool>>, Id<bool>}
ex_impl!{Nexc<(Id<bool>, Id<bool>)>, Id<bool>}
ex_impl!{Nexc<(Id<bool>, ())>, ()}
ex_impl!{Nexc<((), Id<bool>)>, Id<bool>}
ex_impl!{Nexc<(Not, Id<bool>)>, Id<bool>}
ex_impl!{Nexc<(Id<bool>, Not)>, Not}
ex_impl!{T Add<T>, ()}
ex_impl!{T Even<T>, ()}
ex_impl!{T Even<T, Even<T>>, Id<bool>}
ex_impl!{T Even<T, Odd<T>>, Not}
ex_impl!{T Even<T, (Even<T>, Odd<T>)>}
ex_impl!{T Even<T, (Odd<T>, Even<T>)>}
ex_impl!{T Even<T, (Even<T>, Even<T>)>}
ex_impl!{T Even<T, (Odd<T>, Odd<T>)>}
ex_impl!{T Odd<T>, ()}
ex_impl!{T Odd<T, Odd<T>>, Id<bool>}
ex_impl!{T Odd<T, Even<T>>, Not}

#[macro_use]
mod macros;
mod nat;

macro_rules! nat_nat_impl {
    ($t:ident) => {
        ex_impl!{Add<$t, (Even<$t>, Odd<$t>)>, Odd<$t>}
        ex_impl!{Add<$t, (Odd<$t>, Even<$t>)>, Odd<$t>}
        ex_impl!{Add<$t, (Even<$t>, Even<$t>)>, Even<$t>}

        // `∃add{(odd, odd)} => if((< 2), false_1, even)`
        impl ExPath for Add<$t, (Odd<$t>, Odd<$t>)> {
            type Lift = If<LtK<$t>, False1<$t>, Even<$t>>;
            fn ex_path(&self) -> Self::Lift {
                If {co: LtK {k: 2, i: ()}, tr: False1::default(), fa: Even::default(), i: ()}
            }
        }
    }
}

nat_nat_impl!{u8}
nat_nat_impl!{u16}
nat_nat_impl!{u32}
nat_nat_impl!{u64}
