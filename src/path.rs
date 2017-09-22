use *;

pub trait Path<T> {
    type Lift;

    fn path_force(&self, arg: T) -> <Self as Path<T>>::Lift;

    /// Can call method if the existential paths of constrained input matches.
    fn path(&self, arg: T) -> <Self as Path<T>>::Lift
        where <Self as Path<T>>::Lift: ExPath<
                    Lift = <<T as Constrain<<Self as ExPath>::Lift>>::Lift as ExPath>::Lift>,
              T: Constrain<<Self as ExPath>::Lift>,
              <T as Constrain<<Self as ExPath>::Lift>>::Lift: ExPath,
              Self: ExPath
    {
        self.path_force(arg)
    }
}

macro_rules! path_impl {
    (sym $a:ident , $b:ident , $c:ident) => {
        impl<T: Clone> Path<$b> for $a<T>
            where $b<T>: ExPath
        {
            type Lift = $c<<<$b as Constrain<T>>::Lift as ExPath>::Lift>;

            fn path_force(&self, arg: $b) -> Self::Lift {
                $c {i: arg.i_force(self.i.clone()).ex_path()}
            }
        }
    };
    (sym $a:ident , $b:ident , $c:ident < $t:ident >) => {
        impl<T: Clone> Path<$b> for $a<T>
            where $b<T>: ExPath
        {
            type Lift = $c<$t, <<$b as Constrain<T>>::Lift as ExPath>::Lift>;

            fn path_force(&self, arg: $b) -> Self::Lift {
                $c {t: PhantomData, i: arg.i_force(self.i.clone()).ex_path()}
            }
        }
    };
    (sym $a:ident < $t:ident >, $b:ident , $c:ident) => {
        impl<T: Clone> Path<$b> for $a<$t, T>
            where $b<T>: ExPath
        {
            type Lift = $c<<<$b as Constrain<T>>::Lift as ExPath>::Lift>;

            fn path_force(&self, arg: $b) -> Self::Lift {
                $c {i: arg.i_force(self.i.clone()).ex_path()}
            }
        }
    };
    (sym $a:ident < $t:ident >, $b:ident < $bt:ident >, $c:ident) => {
        impl<T: Clone> Path<$b<$bt>> for $a<$t, T>
            where $b<$bt, T>: ExPath
        {
            type Lift = $c<<<$b<$bt> as Constrain<T>>::Lift as ExPath>::Lift>;

            fn path_force(&self, arg: $b<$bt>) -> Self::Lift {
                $c {i: arg.i_force(self.i.clone()).ex_path()}
            }
        }
    };
    (sym $a:ident < $t:ident >, $b:ident < $bt:ident >, $c:ident < $t2:ident >) => {
        impl<T: Clone> Path<$b<$bt>> for $a<$t, T>
            where $b<$bt, T>: ExPath
        {
            type Lift = $c<$t2, <<$b<$bt> as Constrain<T>>::Lift as ExPath>::Lift>;

            fn path_force(&self, arg: $b<$bt>) -> Self::Lift {
                $c {t: PhantomData, i: arg.i_force(self.i.clone()).ex_path()}
            }
        }
    };
    ($a:ident , $b:ident , $c:ident) => {
        impl Path<$b> for $a {
            type Lift = $c;

            fn path_force(&self, _: $b) -> Self::Lift {
                $c::default()
            }
        }
    }
}

path_impl!{sym Or, Not, And}
path_impl!{sym And, Not, Or}
path_impl!{sym Eq<bool>, Not, Xor}
path_impl!{sym Xor, Not, Eq<bool>}
path_impl!{sym Nor, Not, Nand}
path_impl!{sym Nand, Not, Nor}
path_impl!{sym Exc, Not, Nrexc}
path_impl!{sym Nrexc, Not, Exc}
path_impl!{sym Rexc, Not, Nexc}
path_impl!{sym Nexc, Not, Rexc}

macro_rules! nat_impl {
    ($t:ident) => {
        path_impl!{sym Add<$t>, Even<$t>, Eq<bool>}
        path_impl!{sym Add<$t>, Odd<$t>, Xor}
    };
}

nat_impl!{u8}
nat_impl!{u16}
nat_impl!{u32}
nat_impl!{u64}
