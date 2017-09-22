
macro_rules! reduce_if_impl {
    (co : $co:ty , tr : $tr:ty , fa : $fa:ty , $con:ty => $r:ident < $rt:ident >) => {
        impl ExPath for If<$co, $tr, $fa, $con> {
            type Lift = <$r<$rt> as ExPath>::Lift;

            fn ex_path(&self) -> Self::Lift {
                $r {k: self.co.k, i: ()}.ex_path()
            }
        }
    };
}
