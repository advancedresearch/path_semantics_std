use *;

/// Trivial path of constrain function.
pub trait TriPath {
    type Lift;

    fn tri_path(&self) -> Self::Lift;
}

impl<T, Co, Tr, Fa, I: Clone> TriPath for IfK<T, Co, Tr, Fa, I> {
    type Lift = I;
    fn tri_path(&self) -> Self::Lift {self.i.clone()}
}

impl<Co, Tr, Fa, I: Clone> TriPath for If<Co, Tr, Fa, I> {
    type Lift = I;
    fn tri_path(&self) -> Self::Lift {self.i.clone()}
}

macro_rules! tri_path_impl {
    ($a:ident t) => {
        impl<T, I: Clone> TriPath for $a<T, I> {
            type Lift = I;
            fn tri_path(&self) -> Self::Lift {self.i.clone()}
        }
    };
    ($a:ident) => {
        impl<I: Clone> TriPath for $a<I> {
            type Lift = I;
            fn tri_path(&self) -> Self::Lift {self.i.clone()}
        }
    };
}

tri_path_impl!{False1 t}
tri_path_impl!{Id t}
tri_path_impl!{Not}
tri_path_impl!{Or}
tri_path_impl!{And}
tri_path_impl!{Eq t}
tri_path_impl!{EqK t}
tri_path_impl!{Xor}
tri_path_impl!{Nor}
tri_path_impl!{Nand}
tri_path_impl!{Exc}
tri_path_impl!{Nrexc}
tri_path_impl!{Rexc}
tri_path_impl!{Nexc}
tri_path_impl!{Even t}
tri_path_impl!{Odd t}
tri_path_impl!{Add t}
tri_path_impl!{AddK t}
tri_path_impl!{GeK t}
tri_path_impl!{LtK t}
