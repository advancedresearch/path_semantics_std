use *;

macro_rules! nat_impl {
    ($t:ident , max : $($max:tt)*) => {
        ex_impl!{K AddK<$t>, GeK<$t>}
        ex_impl!{If<GeK<$t>, Even<$t>, Odd<$t>>, ()}
        ex_impl!{If<GeK<$t>, Odd<$t>, Even<$t>>, ()}
        ex_impl!{If<LtK<$t>, Even<$t>, Odd<$t>>, ()}
        ex_impl!{If<LtK<$t>, Odd<$t>, Even<$t>>, ()}
        ex_impl!{If<GeK<$t>, IfK<$t, Odd<$t>, Even<$t>, Odd<$t>>, False1<$t>>, ()}
        // `∃if((< k), false_1, even)`
        // `k == 0 => ∃if((< 0), false_1, even)`
        // `          ∃if(false, false_1, even)`
        // `          ∃even`
        // `          true_1`
        // `\(x: bool) = if k == 0 {true_1} else {true_1}`
        ex_impl!{If<LtK<$t>, False1<$t>, Even<$t>>, ()}
        // `∃even{if((< k), false_1, even)} => id`
        ex_impl!{Even<$t, If<LtK<$t>, False1<$t>, Even<$t>>>, Id<bool>}

        // `∃even{(= k)}`
        // `\(x) = if even(k) {id(x)} else {not(x)}`
        impl ExPath for Even<$t, EqK<$t>> {
            type Lift = IfK<$t, Even<$t>, Id<bool>, Not>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.i.k, co: Even::default(), tr: Id::default(), fa: Not::default(), i: ()}
            }
        }

        impl ExPath for GeK<$t> {
            type Lift = IfK<$t, EqK<$t>, Id<bool>, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.k, co: EqK {k: 0, i: ()}, tr: Id::default(), fa: (), i: ()}
            }
        }

        impl ExPath for LtK<$t> {
            type Lift = IfK<$t, EqK<$t>, Not, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.k, co: EqK {k: 0, i: ()}, tr: Not::default(), fa: (), i: ()}
            }
        }

        // `∃(>= k){even}`
        // `\(x: bool) = if k == max {not(x)} else {true_1(x)}`
        // The maxium value of an unsigned integer is an odd number.
        // If `k` is set to this number, then there exists no greater even number.
        // When that is the case, the `(>= k){even}` function always returns `false`.
        impl ExPath for GeK<$t, Even<$t>> {
            type Lift = IfK<$t, EqK<$t>, Not, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.k, co: EqK {k: $($max)*, i: ()}, tr: Not::default(), fa: (), i: ()}
            }
        }

        // `∃(>= k){odd}`
        // `\(x: bool) = if k == max {id(x)} else {true_1(x)}`
        // The maxium value of an unsigned integer is an odd number.
        // When that is the case, the `(>= k){even}` function always returns `true`.
        impl ExPath for GeK<$t, Odd<$t>> {
            type Lift = IfK<$t, EqK<$t>, Id<bool>, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.k, co: EqK {k: $($max)*, i: ()}, tr: Id::default(), fa: (), i: ()}
            }
        }

        // `∃(< k){even}`
        // `\(x: bool) = if k == 0 {not(x)} else {true_1(x)}`
        impl ExPath for LtK<$t, Even<$t>> {
            type Lift = IfK<$t, EqK<$t>, Not, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.k, co: EqK {k: 0, i: ()}, tr: Not::default(), fa: (), i: ()}
            }
        }

        // `∃(< k){odd}`
        // ```ignore
        // k == 0 => ∃(< 0){odd} => ∃false_1{odd} ∃false_1 => not
        // k == 1 => ∃(< 1){odd} => ∃false_1 => not
        // k == 2 => ∃(< 2){odd} => true_1
        // ```
        // `\(x: bool) = if k < 2 {not(x)} else {true_1(x)}`
        impl ExPath for LtK<$t, Odd<$t>> {
            type Lift = IfK<$t, LtK<$t>, Not, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.k, co: LtK {k: 0, i: ()}, tr: Not::default(), fa: (), i: ()}
            }
        }

        impl ExPath for EqK<$t, Even<$t>> {
            type Lift = IfK<$t, Even<$t>, (), Not>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.k, co: Even::default(), tr: (), fa: Not::default(), i: ()}
            }
        }

        impl ExPath for EqK<$t, Odd<$t>> {
            type Lift = IfK<$t, Odd<$t>, (), Not>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.k, co: Odd::default(), tr: (), fa: Not::default(), i: ()}
            }
        }

        // `∃add(k){even}`
        // `\(x: nat) = if x >= k {if even(k) {even(x)} else {odd(x)}} else {false}`
        impl ExPath for AddK<$t, Even<$t>> {
            type Lift = If<GeK<$t>, IfK<$t, Even<$t>, Even<$t>, Odd<$t>>, False1<$t>>;
            fn ex_path(&self) -> Self::Lift {
                If {
                    co: GeK {k: self.k, i: ()},
                    tr: IfK {k: self.k, co: Even::default(), tr: Even::default(), fa: Odd::default(), i: ()},
                    fa: False1::default(), i: ()
                }
            }
        }

        // `∃add(k){odd}`
        // `\(x: nat) = if x >= k {if odd(k) {even(x)} else {odd(x)}} else {false}`
        impl ExPath for AddK<$t, Odd<$t>> {
            type Lift = If<GeK<$t>, IfK<$t, Odd<$t>, Even<$t>, Odd<$t>>, False1<$t>>;
            fn ex_path(&self) -> Self::Lift {
                If {
                    co: GeK {k: self.k, i: ()},
                    tr: IfK {k: self.k, co: Odd::default(), tr: Even::default(), fa: Odd::default(), i: ()},
                    fa: False1::default(), i: ()
                }
            }
        }

        // `∃if((>= k), if even(k) {even} else {odd}, false_1)`
        // `\(x: bool) = if even(k) {true_1(x)} else {not(x)}`
        impl ExPath for If<GeK<$t>, IfK<$t, Even<$t>, Even<$t>, Odd<$t>>, False1<$t>> {
            type Lift = IfK<$t, Even<$t>, (), Not>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.co.k, co: Even::default(), tr: (), fa: Not::default(), i: ()}
            }
        }

        // `∃if((< k), odd, even){(= k2)}`
        // `\(x: bool) = if k2 < k {if odd(k2) {id(x)} else {not(x)}} else {if even(k2) {id(x)} else {not{x}}}`
        impl ExPath for If<LtK<$t>, Odd<$t>, Even<$t>, EqK<$t>> {
            type Lift = IfK<$t, LtK<$t>,
                            IfK<$t, Odd<$t>, Id<bool>, Not>,
                            IfK<$t, Even<$t>, Id<bool>, Not>
                        >;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, i: (),
                    co: self.co.clone(),
                    tr: IfK {k: self.i.k, co: Odd::default(), tr: Id::default(), fa: Not::default(), i: ()},
                    fa: IfK {k: self.i.k, co: Even::default(), tr: Id::default(), fa: Not::default(), i: ()},
                }
            }
        }

        // `∃if((< k), even, odd){(= k2)}`
        // `\(x: bool) = if k2 < k {if even(k2) {id(x)} else {not(x)}} else {if odd(k2) {id(x)} else {not(x)}}`
        impl ExPath for If<LtK<$t>, Even<$t>, Odd<$t>, EqK<$t>> {
            type Lift = IfK<$t, LtK<$t>,
                            IfK<$t, Even<$t>, Id<bool>, Not>,
                            IfK<$t, Odd<$t>, Id<bool>, Not>
                        >;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, i: (),
                    co: self.co.clone(),
                    tr: IfK {k: self.i.k, co: Even::default(), tr: Id::default(), fa: Not::default(), i: ()},
                    fa: IfK {k: self.i.k, co: Odd::default(), tr: Id::default(), fa: Not::default(), i: ()},
                }
            }
        }

        // `∃if((>= k), odd, even){(= k2)}`
        // `\(x: bool) = if k2 >= k {if odd(k2) {id(x)} else {not(x)}} else {if even(k2) {id(x)} else {not(x)}}`
        impl ExPath for If<GeK<$t>, Odd<$t>, Even<$t>, EqK<$t>> {
            type Lift = IfK<$t, GeK<$t>,
                            IfK<$t, Odd<$t>, Id<bool>, Not>,
                            IfK<$t, Even<$t>, Id<bool>, Not>
                        >;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, i: (), co: self.co.clone(),
                    tr: IfK {k: self.i.k, co: Odd::default(), tr: Id::default(), fa: Not::default(), i: ()},
                    fa: IfK {k: self.i.k, co: Even::default(), tr: Id::default(), fa: Not::default(), i: ()}
                }
            }
        }

        // `∃if((>= k), even, odd){(= k2)}`
        // `\(x: bool) = if k2 >= k {if even(k2) {id(x)} else {not(x)}} else {if odd(k2) {id(x)} else {not(x)}}`
        impl ExPath for If<GeK<$t>, Even<$t>, Odd<$t>, EqK<$t>> {
            type Lift = IfK<$t, GeK<$t>,
                            IfK<$t, Even<$t>, Id<bool>, Not>,
                            IfK<$t, Odd<$t>, Id<bool>, Not>
                        >;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, i: (), co: self.co.clone(),
                    tr: IfK {k: self.i.k, co: Even::default(), tr: Id::default(), fa: Not::default(), i: ()},
                    fa: IfK {k: self.i.k, co: Odd::default(), tr: Id::default(), fa: Not::default(), i: ()}
                }
            }
        }

        // `∃odd{(= k)}`
        // `\(x: bool) = if odd(k) {id(x)} else {not(x)}`
        impl ExPath for Odd<$t, EqK<$t>> {
            type Lift = IfK<$t, Odd<$t>, Id<bool>, Not>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.i.k, co: Odd::default(), tr: Id::default(), fa: Not::default(), i: ()}
            }
        }

        // `∃(= k){= k2}`
        // `\(x: bool) = if k == k2 {id(x)} else {not(x)}`
        impl ExPath for EqK<$t, EqK<$t>> {
            type Lift = IfK<$t, EqK<$t>, Id<bool>, Not>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.i.k, co: EqK {k: self.k, i: ()}, tr: Id::default(), fa: Not::default(), i: ()}
            }
        }

        // `∃(< k){= k2}`
        // `\(x: bool) = if k2 < k {id(x)} else {not(x)}`
        impl ExPath for LtK<$t, EqK<$t>> {
            type Lift = IfK<$t, LtK<$t>, Id<bool>, Not>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.i.k, co: LtK {k: self.k, i: ()}, tr: Id::default(), fa: Not::default(), i: ()}
            }
        }

        // `∃(>= k){= k2}`
        // `\(x: bool) = if k2 >= k {id(x)} else {not(x)}`
        impl ExPath for GeK<$t, EqK<$t>> {
            type Lift = IfK<$t, GeK<$t>, Id<bool>, Not>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.i.k, co: GeK {k: self.k, i: ()}, tr: Id::default(), fa: Not::default(), i: ()}
            }
        }

        // `∃add(k){= k2} => (= k + k2)`
        impl ExPath for AddK<$t, EqK<$t>> {
            type Lift = EqK<$t>;
            fn ex_path(&self) -> Self::Lift {
                EqK {k: self.k + self.i.k, i: ()}
            }
        }

        // `∃even{(>= k)}`
        // `\(x: bool) = if k == max {not(x)} else {true_1(x)}`
        // There is no even number greater or equal to the largest unsigned integer.
        impl ExPath for Even<$t, GeK<$t>> {
            type Lift = IfK<$t, EqK<$t>, Not, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.i.k, co: EqK {k: $($max)*, i: ()}, tr: Not::default(), fa: (), i: ()}
            }
        }

        // `∃if((< k), odd, even){(>= k2)}`
        // `\(x: bool) = if ... {...} else {...}`
        // `k2 >= k => not`
        // `∃odd{(>= k2)} | ∃even{(>= k2)}`
        // `∃even{(>= k2)} => if k2 == max {not} else {true_1}`
        // `∃odd{(>= k2)} => if k2 == max {id} else {true_1}`
        // `k == max => k2 < max`
        // `\(x: bool) = if k2 >= k {not(x)} else {true_1}`
        impl ExPath for If<LtK<$t>, Odd<$t>, Even<$t>, GeK<$t>> {
            type Lift = IfK<$t, GeK<$t>, Not, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.i.k, co: GeK {k: self.co.k, i: ()}, tr: Not::default(), fa: (), i: ()}
            }
        }

        // `∃if((< k), even, odd){(>= k)}`
        // `\(x: bool) = if k2 >= k {not(x)} else {true_1}`
        impl ExPath for If<LtK<$t>, Even<$t>, Odd<$t>, GeK<$t>> {
            type Lift = IfK<$t, GeK<$t>, Not, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.i.k, co: GeK {k: self.co.k, i: ()}, tr: Not::default(), fa: (), i: ()}
            }
        }

        // `∃if((>= k), odd, even){(>= k2)}`
        // `k2 == max => ∃if((>= k), odd, even){(>= max)}`
        // `             ∃if((>= k), odd, even){(= max)} => k <= max`
        // `             ∃odd{(= max)}`
        // `             id`
        // `\(x: bool) = if k2 == max {id(x)} else {true_1(x)}}`
        impl ExPath for If<GeK<$t>, Odd<$t>, Even<$t>, GeK<$t>> {
            type Lift = IfK<$t, EqK<$t>, Id<bool>, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.i.k, co: EqK {k: $($max)*, i: ()}, tr: Id::default(), fa: (), i: ()}
            }
        }

        // `∃if((> k), even, odd){(>= k2)}`
        // `\(x: bool) = if k2 == max {not(x)} else {true_1(x)}`
        impl ExPath for If<GeK<$t>, Even<$t>, Odd<$t>, GeK<$t>> {
            type Lift = IfK<$t, EqK<$t>, Not, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.i.k, co: EqK {k: $($max)*, i: ()}, tr: Not::default(), fa: (), i: ()}
            }
        }

        // `∃odd{(>= k)}`
        // `\(x: bool) = if k == max {id(x)} else {true_1(x)}`
        impl ExPath for Odd<$t, GeK<$t>> {
            type Lift = IfK<$t, EqK<$t>, Id<bool>, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.i.k, co: EqK {k: $($max)*, i: ()}, tr: Id::default(), fa: (), i: ()}
            }
        }

        // `∃(= k){>= k2}`
        // `\(x: bool) = if k < k2 {not(x)} else {if k2 == max {if k == max {id(x)} else {true_1}} else {true_1}}`
        impl ExPath for EqK<$t, GeK<$t>> {
            type Lift = IfK<$t, LtK<$t>, Not, IfK<$t, EqK<$t>, IfK<$t, EqK<$t>, Id<bool>, ()>, ()>>;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.k, i: (),
                    co: LtK {k: self.i.k, i: ()},
                    tr: Not::default(),
                    fa: IfK {k: self.i.k, co: EqK {k: $($max)*, i: ()},
                        tr: IfK {k: self.k, co: EqK {k: $($max)*, i: ()}, tr: Id::default(), fa: (), i: ()},
                        fa: (),
                        i: ()
                    },
                }
            }
        }

        // `∃(< k){(>= k2)}`
        // `\(x: bool) = if k2 >= k {not(x)} else {if k == 0 {not(x)} else {true_1}}`
        impl ExPath for LtK<$t, GeK<$t>> {
            type Lift = IfK<$t, GeK<$t>, Not, IfK<$t, EqK<$t>, Not, ()>>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.i.k, co: GeK {k: self.k, i: ()}, tr: Not::default(),
                     fa: IfK {k: self.k, co: EqK {k: 0, i: ()}, tr: Not::default(), fa: (), i: ()}, i: ()}
            }
        }

        // `∃(>= k){(>= k2)}`
        // `k2 == max => ∃(>= k){(>= max)}`
        // `             ∃(>= k){(= max)} => k <= max`
        // `             id`
        // `k == 0 => ∃(>= 0){(>= k2)}`
        // `          ∃true_1{(>= k2)}`
        // `          ∃true_1`
        // `          id`
        // `k > k2 => true_1 else id
        // `\(x: bool) = if k2 < k {true_1(x)} else {id(x)}`
        impl ExPath for GeK<$t, GeK<$t>> {
            type Lift = IfK<$t, LtK<$t>, (), Id<bool>>;
            fn ex_path(&self) -> Self::Lift {
                IfK {k: self.i.k, co: LtK {k: self.k, i: ()}, tr: (), fa: Id::default(), i: ()}
            }
        }

        // `∃add(k){(>= k2)} <=> (>= k + k2)`
        impl ExPath for AddK<$t, GeK<$t>> {
            type Lift = GeK<$t>;
            fn ex_path(&self) -> Self::Lift {
                GeK {k: self.k + self.i.k, i: ()}
            }
        }

        // `∃even{(< k)}`
        // `k == 0 => ∃even{(< 0)} => false_1`
        // `k == 1 => ∃even{(< 1)} => id`
        // `k == 2 => ∃even{(< 2)} => true_1`
        // `\(x: bool) = if k < 2 {if k == 0 {not(x)} else {id(x)}} else {true_1(x)}`
        impl ExPath for Even<$t, LtK<$t>> {
            type Lift = IfK<$t, LtK<$t>, IfK<$t, EqK<$t>, False1<bool>, Id<bool>>, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, co: LtK {k: 2, i: ()},
                    tr: IfK {k: self.i.k, co: EqK {k: 0, i: ()}, tr: False1::default(), fa: Id::default(), i: ()},
                    fa: (), i: ()
                }
            }
        }

        // `∃if((< k), odd, even){(< k2)}`
        // `k2 == 0 => ∃if((< k), odd, even){(< 0)} => false_1`
        // `k2 == 1 => ∃if((< k), odd, even){(< 1)}`
        // `           ∃if((< k), odd, even){(= 0)}`
        // `           ∃if((< k), false, true)`
        // `           ∃(>= k)`
        // `k2 == 2 => ∃if((< k), odd, even){(< 2)} => true_1`
        // `\(x: bool) = if k2 < 2 {if k2 == 0 {false_1(x)} else {(∃(>= k))(x)}} else {true_1(x)}`
        impl ExPath for If<LtK<$t>, Odd<$t>, Even<$t>, LtK<$t>> {
            type Lift = IfK<$t, LtK<$t>, IfK<$t, EqK<$t>, False1<bool>, <GeK<$t> as ExPath>::Lift>, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, co: LtK {k: 2, i: ()}, i: (),
                    tr: IfK {k: self.i.k, co: EqK {k: 0, i: ()}, tr: False1::default(),
                                fa: GeK {k: self.co.k, i: ()}.ex_path(), i: ()},
                    fa: ()
                }
            }
        }

        // `∃if((< k), even, odd){(< k2)}`
        // `k2 == 0 => ∃if((< k), even, odd){(< 0)} => false_1`
        // `k2 == 1 => ∃if((< k), even, odd){(< 1)}`
        // `           ∃if((< k), even, odd){(= 0)}`
        // `           ∃if((< k), true, false)`
        // `           ∃(< k)`
        // `k2 == 2 => ∃if((< k), even, odd){(< 2)} => true_1`
        // `\(x: bool) = if k2 < 2 {if k2 == 0 {false_1(x)} else {(∃(< k))(x)}} else {true_1(x)}`
        impl ExPath for If<LtK<$t>, Even<$t>, Odd<$t>, LtK<$t>> {
            type Lift = IfK<$t, LtK<$t>, IfK<$t, EqK<$t>, False1<bool>, <LtK<$t> as ExPath>::Lift>, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, co: LtK {k: 2, i: ()}, i: (),
                    tr: IfK {k: self.i.k, co: EqK {k: 0, i: ()}, tr: False1::default(),
                             fa: LtK {k: self.co.k, i: ()}.ex_path(), i: ()},
                    fa: ()
                }
            }
        }

        // `∃if((>= k), odd, even){(< k2)}`
        // `k2 == 0 => ∃if((>= k), odd, even){(< 0)} => false_1`
        // `k2 == 1 => ∃if((>= k), odd, even){(< 1)}`
        // `           ∃if((>= k), odd, even){(= 0)}`
        // `           ∃if((>= k), false, true)`
        // `           ∃(< k)`
        // `k2 == 2 => ∃if((>= k), odd, even){(< 2)} => true_1`
        // `\(x: bool) = if k2 < 2 {if k2 == 0 {false_1(x)} else {(∃(< k))(x)}} else {true_1}`
        impl ExPath for If<GeK<$t>, Odd<$t>, Even<$t>, LtK<$t>> {
            type Lift = IfK<$t, LtK<$t>, IfK<$t, EqK<$t>, False1<bool>, <LtK<$t> as ExPath>::Lift>, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, co: LtK {k: 2, i: ()}, i: (),
                    tr: IfK {k: self.i.k, co: EqK {k: 0, i: ()}, tr: False1::default(),
                             fa: LtK {k: self.co.k, i: ()}.ex_path(), i: ()},
                    fa: ()
                }
            }
        }

        // `∃if((>= k), even, odd){(< k2)}`
        // `k2 == 0 => ∃if((>= k), even, odd){(< 0)} => false_1`
        // `k2 == 1 => ∃if((>= k), even, odd){(< 1)}`
        // `           ∃if((>= k), even, odd){(= 0)}`
        // `           ∃if((>= k), true, false)`
        // `           ∃(>= k)`
        // `k2 == 2 => ∃if((>= k), even, odd){(< 2)} => true_1`
        // `\(x: bool) = if k2 < 2 {if k == 0 {false_1(x)} else {(∃(>= k))(x)}} else {true_1(x)}`
        impl ExPath for If<GeK<$t>, Even<$t>, Odd<$t>, LtK<$t>> {
            type Lift = IfK<$t, LtK<$t>, IfK<$t, EqK<$t>, False1<bool>, <GeK<$t> as ExPath>::Lift>, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, co: LtK {k: 2, i: ()}, i: (),
                    tr: IfK {k: self.i.k, co: EqK {k: 0, i: ()}, tr: False1::default(),
                             fa: GeK {k: self.co.k, i: ()}.ex_path(), i: ()},
                    fa: ()
                }
            }
        }

        // `∃odd{(< k)}`
        // `k == 0 => ∃odd{(< 0)} => false_1`
        // `k == 1 => ∃odd{(< 1)} => ∃odd{(= 0)} => not`
        // `k == 2 => ∃odd{(< 2)} => true_1`
        // `\(x: bool) = if k < 2 {if k == 0 {false_1(x)} else {not(x)}} else {true_1}`
        impl ExPath for Odd<$t, LtK<$t>> {
            type Lift = IfK<$t, LtK<$t>, IfK<$t, EqK<$t>, False1<bool>, Not>, ()>;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, co: LtK {k: 2, i: ()}, i: (),
                    tr: IfK {k: self.i.k, co: EqK {k: 0, i: ()}, tr: False1::default(),
                             fa: Not::default(), i: ()},
                    fa: ()
                }
            }
        }

        // `∃(= k){(< k2)}`
        // `k2 == 0 => false_1`
        // `k2 >= k => not`
        //          else true_1`
        // `\(x: bool) = if k2 == 0 {false_1(x)} else {if k2 >= k {not(x)} else {true_1(x)}}`
        impl ExPath for EqK<$t, LtK<$t>> {
            type Lift = IfK<$t, EqK<$t>, False1<bool>, IfK<$t, GeK<$t>, Not, ()>>;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, co: EqK {k: 0, i: ()}, i: (),
                    tr: False1::default(),
                    fa: IfK {k: self.i.k, co: GeK {k: self.k, i: ()}, tr: Not::default(), fa: (), i: ()}
                }
            }
        }

        // `∃(< k){(< k2)}`
        // `k2 == 0 => `∃(< k){(< 0)} => false_1`
        // `k == 0` => not
        // `k >= k2 => id else true_1`
        // `\(x: bool) = if k2 == 0 {false_1(x)} else {if k == 0 {not(x)} else {if k >= k2 {id(x)} else {true_1(x)}}}`
        impl ExPath for LtK<$t, LtK<$t>> {
            type Lift = IfK<$t, EqK<$t>, False1<bool>,
                            IfK<$t, EqK<$t>, Not, IfK<$t, GeK<$t>, Id<bool>, ()>>
                        >;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, co: EqK {k: 0, i: ()}, i: (),
                    tr: False1::default(),
                    fa: IfK {
                        k: self.k, co: EqK {k: 0, i: ()}, tr: Not::default(),
                        fa: IfK {k: self.k, co: GeK {k: self.i.k, i: ()},
                                 tr: Id::default(), fa: (), i: ()}, i: ()
                    }
                }
            }
        }

        // `∃(>= k){(< k2)}`
        // `k2 == 0 => false_1`
        // `k == 0 => id else true_1`
        // `\(x: bool) = if k2 == 0 {false_1(x)} else {if k == 0 {id(x)} else {true_1(x)}}`
        impl ExPath for GeK<$t, LtK<$t>> {
            type Lift = IfK<$t, EqK<$t>, False1<bool>, IfK<$t, EqK<$t>, Id<bool>, ()>>;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, co: EqK {k: 0, i: ()}, tr: False1::default(), i: (),
                    fa: IfK {k: self.k, co: EqK {k: 0, i: ()}, tr: Id::default(), fa: (), i: ()}
                }
            }
        }

        // `∃add(k){(< k2)}`
        // `k2 == 0 => false_1`
        // `[k, k + k2)`
        // `\(x: nat) = if k2 == 0 {false_1(x)} else {if x >= k {(< k + k2)(x)} else {false_1(x)}}`
        impl ExPath for AddK<$t, LtK<$t>> {
            type Lift = IfK<$t, EqK<$t>, False1<$t>, If<GeK<$t>, LtK<$t>, False1<$t>>>;
            fn ex_path(&self) -> Self::Lift {
                IfK {
                    k: self.i.k, co: EqK {k: 0, i: ()}, i: (), tr: False1::default(),
                    fa: If {co: GeK {k: self.k, i: ()}, tr: LtK {k: self.k + self.i.k, i: ()},
                            fa: False1::default(), i: ()}
                }
            }
        }

        // `∃if((>= k), even, odd){even} => ∃(>= k)`
        reduce_if_impl!{co: GeK<$t>, tr: Even<$t>, fa: Odd<$t>, Even<$t> => GeK<$t>}
        // `∃if((>= k), even, odd){odd} => ∃(< k)`
        reduce_if_impl!{co: GeK<$t>, tr: Even<$t>, fa: Odd<$t>, Odd<$t> => LtK<$t>}
        // `∃if((>= k), odd, even){even} => ∃(< k)`
        reduce_if_impl!{co: GeK<$t>, tr: Odd<$t>, fa: Even<$t>, Even<$t> => LtK<$t>}
        // `∃if((>= k), odd, even){odd} => ∃(>= k)`
        reduce_if_impl!{co: GeK<$t>, tr: Odd<$t>, fa: Even<$t>, Odd<$t> => GeK<$t>}
        // `∃if((< k), even, odd){even} => ∃(< k)`
        reduce_if_impl!{co: LtK<$t>, tr: Even<$t>, fa: Odd<$t>, Even<$t> => LtK<$t>}
        // `∃if((< k), even, odd){odd} => ∃(>= k)`
        reduce_if_impl!{co: LtK<$t>, tr: Even<$t>, fa: Odd<$t>, Odd<$t> => GeK<$t>}
        // `∃if((< k), odd, even){even} => ∃(>= k)`
        reduce_if_impl!{co: LtK<$t>, tr: Odd<$t>, fa: Even<$t>, Even<$t> => GeK<$t>}
        // `∃if((< k), odd, even){odd} => ∃(< k)`
        reduce_if_impl!{co: LtK<$t>, tr: Odd<$t>, fa: Even<$t>, Odd<$t> => LtK<$t>}

    };
}

nat_impl!{u8, max: ::std::u8::MAX}
nat_impl!{u16, max: ::std::u16::MAX}
nat_impl!{u32, max: ::std::u32::MAX}
nat_impl!{u64, max: ::std::u64::MAX}
