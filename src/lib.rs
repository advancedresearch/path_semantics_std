//! # path_semantics_std
//! A Rust type checked implementation of the standard dictionary of path semantics using constrained functions
//!
//! *Notice! This library is in early stage of development and might contain bugs and missing features!*
//!
//! ### Example: Proving addition of even numbers
//!
//! ```rust
//! // Prove `add[even] <=> eq`, which is equal to
//! // `even(add(a, b)) = eq(even(a), even(b))`.
//! let add: Add<u32> = Add::default();
//! let even: Even<u32> = Even::default();
//! let path: Eq<bool> = add.path(even);
//! ```
//!
//! The Rust type checker proves equivalence of existential paths when calling `.path`.
//! It is based on a neat theory of path semantics called "constrained functions".
//! All you need to do is expressing the theorem directly in Rust code!
//!
//! The example above can be shortened down to a single line:
//!
//! ```rust
//! let path: Eq<bool> = Add::<u32>::default().path(Even::default());
//! ```
//!
//! To change the constrains, use the `.i` method (using variable names for readability):
//!
//! ```rust
//! let path: Eq<bool, (Id<bool>, Not)> = add.i((even, odd)).path(even);
//! ```
//!
//! This changes the `add` function into a partial function,
//! and it propagates the constraint such that you can see the constraint on the predictor function.
//!
//! The `.ex_path` method returns an output function:
//!
//! ```rust
//! let res: Not = add.i((even, odd)).path(even).ex_path();
//! ```
//!
//! In this case we proved that if you add an even number and an odd number, you don't get an even number!
//!
//! ### What is path semantics?
//!
//! A brief introduction is given here, since most people do not know what it is.
//! For more information about path semantics, click [here](https://github.com/advancedresearch/path_semantics).
//!
//! Path semantics is an attempt to make deep ideas in mathematics more accessible and theorem proving more understandable for programmers.
//! It is an extension and unification of [dependently types](https://en.wikipedia.org/wiki/Dependent_type) and [guarded commands](https://en.wikipedia.org/wiki/Guarded_Command_Language), that are used today to reason about and verify software.
//! The major difference from existing work is that path semantics is very high level (more expressive) and allows arbitrary constraints and properties defined by functions.
//! This makes path semantics in general undecidable, but it has rules that allows checking for consistency for specific problems,
//! plus the strict concept of function identity that is used when extending the theory to new domains.
//!
//! The syntax and notation of path semantics is designed to be concise and easily adapted to source code.
//!
//! - `f{g}` means "constrain `f : A -> B` with `g : A -> bool`".
//! - `∀f` means "get the constraint of input of `f`".
//! - Existential path: `∃f : B -> bool` means "what does `f : A -> B` outputs? This depends on the constraint.
//! - Path: `f[g] <=> h` means "the property `g : A -> B` of `f : A -> A` is predicted by `h : B -> B`.
//! - Composition: `g . f` outputs `∃g{∃f}`.
//! - Sub-type: `x : [g] a` where `g : X -> A`, is consistent if `a : [∃g] true`.
//! - Naming of functions: `false_1, not, id, true_1: bool -> bool` (`id` is generic `A -> A`).
//! - Surjective xor non-surjective: All "normal" functions has `∃∃f => {id, true_1}`.
//! - Reduction of proof: `a : [f] b ∧ [g] c` is equal to `a : [f{[g] c}] b` or `a : [g{[f] b}] c`.
//! - Transform to equations: `f[g] <=> h` gives `g(f(a, b)) = h(g(a), g(b))` (example is for binary functions).
//! - Propagation of constraints to paths: Used for complain-when-wrong type checking.
//! - Probabilistic existential path: Like existential path, but for probability theory.
//! - Probabilistic path: A way to predict properties of output probabilistically from properties of input.
//!
//! The theory of path semantics reveals that functions are related to each other in a natural occuring space called
//! "path semantical space", which precisely defines the identity of all functions.
//! Because the space is organized in a way closely related to the concept of prediction,
//! the research has lot of overlap with artificial intelligence and machine learning.
//! Path semantics is a field that studies how this space is organized and higher order algorithms for extracting
//! and applying knowledge related to perfect and probabilistic prediction.
//! It is not so much about finding solutions to a single problem, but for studying and understanding higher order reasoning to solve large classes of problems.
//!
//! ### Features
//!
//! All objects in this library are higher order representations of constrained functions.
//! This means they do not "compute" but merely construct types of each other, in a way that Rust can type check.
//!
//! - `Constrain` trait (type `.i(<constrain>)`, `.i_force` skips existential path check)
//! - `ExPath` trait (type `.ex_path()`)
//! - `Path` trait (type `.path()`, `.path_force` skips existential path check)
//! - Complete Boolean algebra (all paths checked with all constraints)
//! - Some work on natural numbers
//!
//! One problem is combinatorial explosion because of the complexity of functional spaces.
//! To work around this issue, there are some tricks applied to reduce the number of building blocks,
//! such as using `If` and `IfK` for many non-trivial functions.
//!
//! - `If` has a condition that depends on the argument that is dependend on in the branches
//! - `IfK` has a condition that is decided at higher order, and therefore not depended on in the branches
//!
//! The `()` type is used instead of a `True1` because this looks nicer in Rust.

use std::marker::PhantomData;

pub use constrain::*;
pub use ex_path::*;
pub use path::*;

mod constrain;
mod ex_path;
mod path;
mod display;

#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct False1<T, I = ()> {t: PhantomData<T>, i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Id<T, I = ()> {t: PhantomData<T>, i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Not<I = ()> {i: I}

#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Or<I = ()> {i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct And<I = ()> {i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Eq<T, I = ()> {t: PhantomData<T>, i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct EqK<T, I = ()> {k: T, i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Xor<I = ()> {i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Nor<I = ()> {i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Nand<I = ()> {i: I}
/* TODO: To be implemented later.
/// Checks for non-equivalence. Use `Xor` for booleans.
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Neq<T, I = ()> {t: PhantomData<T>, i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct NeqK<T, I = ()> {k: T, i: I}
*/
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Exc<I = ()> {i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Nrexc<I = ()> {i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Rexc<I = ()> {i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Nexc<I = ()> {i: I}

#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Even<T, I = ()> {t: PhantomData<T>, i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Odd<T, I = ()> {t: PhantomData<T>, i: I}

#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct Add<T, I = ()> {t: PhantomData<T>, i: I}
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct AddK<T, I = ()> {k: T, i: I}

/// `(>= k)`
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct GeK<T, I = ()> {k: T, i: I}
/// `(< k)`
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct LtK<T, I = ()> {k: T, i: I}

/// `\(x) = if co(k) {tr(x)} else {fa(x)}`
/// Technically this could reduce the condition to a `bool`,
/// but preserving the `k` makes it easier to debug.
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct IfK<T, Co, Tr, Fa, I = ()> {k: T, co: Co, tr: Tr, fa: Fa, i: I}
/// `\(x) = if co(x) {tr(x)} else {fa(x)}`
#[derive(Copy, Clone, Default, Debug, PartialEq)]
pub struct If<Co, Tr, Fa, I = ()> {co: Co, tr: Tr, fa: Fa, i: I}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_bool<T>(a: T)
        where T: ExPath + Constrain<()> + Constrain<Not>,
              <T as Constrain<()>>::Lift: ExPath,
              <T as Constrain<Not>>::Lift: ExPath
    {
        let _ = a.ex_path();
        let _ = a.i(());
        let _ = a.i(Not::default());
    }

    fn test_bool_bool<T>(a: T)
        where T: ExPath + Constrain<()> + Constrain<Not> +
                 Constrain<(Not, ())> + Constrain<((), Not)> +
                 Constrain<((), ())> + Constrain<(Not, Not)> +
                 Constrain<(Id<bool>, ())> + Constrain<((), Id<bool>)> +
                 Constrain<(Id<bool>, Id<bool>)> + Constrain<Id<bool>> +
                 Constrain<(Not, Id<bool>)> + Constrain<(Id<bool>, Not)>,
              <T as Constrain<()>>::Lift: ExPath,
              <T as Constrain<Not>>::Lift: ExPath,
              <T as Constrain<(Not, ())>>::Lift: ExPath,
              <T as Constrain<((), Not)>>::Lift: ExPath,
              <T as Constrain<((), ())>>::Lift: ExPath,
              <T as Constrain<(Not, Not)>>::Lift: ExPath,
              <T as Constrain<(Id<bool>, ())>>::Lift: ExPath,
              <T as Constrain<((), Id<bool>)>>::Lift: ExPath,
              <T as Constrain<(Id<bool>, Id<bool>)>>::Lift: ExPath,
              <T as Constrain<Id<bool>>>::Lift: ExPath,
              <T as Constrain<(Not, Id<bool>)>>::Lift: ExPath,
              <T as Constrain<(Id<bool>, Not)>>::Lift: ExPath,
    {
        let _ = a.ex_path();
        let _ = a.i(());
        let _ = a.i(Not::default());
        let _ = a.i((Not::default(), ()));
        let _ = a.i(((), Not::default()));
        let _ = a.i(((), ()));
        let _ = a.i((Not::default(), Not::default()));
        let _ = a.i((Id::default(), ()));
        let _ = a.i(((), Id::default()));
        let _ = a.i((Id::default(), Id::default()));
        let _ = a.i(Id::default());
        let _ = a.i((Not::default(), Id::default()));
        let _ = a.i((Id::default(), Not::default()));
    }

    macro_rules! test_bool_bool_path (
        ($a:ident , $b:ident , not : $not:ident, id_bool : $id_bool:ident) => {
            let _: $b = $a.path($not);
            let _: $b<((), ())> = $a.i(((), ())).path($not);
            let _: $b<Id<bool>> = $a.i($not).path($not);
            let _: $b<(Id<bool>, ())> = $a.i(($not, ())).path($not);
            let _: $b<((), Id<bool>)> = $a.i(((), $not)).path($not);
            let _: $b<(Id<bool>, Id<bool>)> = $a.i(($not, $not)).path($not);
            let _: $b<(Id<bool>, Not)> = $a.i(($not, $id_bool)).path($not);
            let _: $b<(Not, Id<bool>)> = $a.i(($id_bool, $not)).path($not);
            let _: $b<(Not, Not)> = $a.i(($id_bool, $id_bool)).path($not);
        };
        ($a:ident , $b:ident < $bt:ident > , not : $not:ident, id_bool : $id_bool:ident) => {
            let _: $b<$bt> = $a.path($not);
            let _: $b<$bt, ((), ())> = $a.i(((), ())).path($not);
            let _: $b<$bt, Id<bool>> = $a.i($not).path($not);
            let _: $b<$bt, (Id<bool>, ())> = $a.i(($not, ())).path($not);
            let _: $b<$bt, ((), Id<bool>)> = $a.i(((), $not)).path($not);
            let _: $b<$bt, (Id<bool>, Id<bool>)> = $a.i(($not, $not)).path($not);
            let _: $b<$bt, (Id<bool>, Not)> = $a.i(($not, $id_bool)).path($not);
            let _: $b<$bt, (Not, Id<bool>)> = $a.i(($id_bool, $not)).path($not);
            let _: $b<$bt, (Not, Not)> = $a.i(($id_bool, $id_bool)).path($not);
        };
        ( not : $not:ident , id_bool : $id_bool:ident , $( [ $($a:tt)* ] ),+ ) => {
            $(
                test_bool_bool_path!($($a)*, not: $not, id_bool: $id_bool);
            )*
        };
    );

    fn test_nat<T, U: From<u8>>(a: T)
        where T: ExPath + Constrain<()> +
                 Constrain<Even<U>> + Constrain<Odd<U>> +
                 Constrain<EqK<U>> + Constrain<GeK<U>> +
                 Constrain<LtK<U>>,
              <T as ExPath>::Lift: ExPath,
              <<T as ExPath>::Lift as ExPath>::Lift: ExPath,
              U: Default,
              <T as Constrain<()>>::Lift: ExPath,
              <T as Constrain<Even<U>>>::Lift: ExPath,
              <T as Constrain<Odd<U>>>::Lift: ExPath,
              <<T as Constrain<Even<U>>>::Lift as ExPath>::Lift: ExPath,
              <<<T as Constrain<Even<U>>>::Lift as ExPath>::Lift as ExPath>::Lift: ExPath,
              <<T as Constrain<Odd<U>>>::Lift as ExPath>::Lift: ExPath,
              <<<T as Constrain<Odd<U>>>::Lift as ExPath>::Lift as ExPath>::Lift: ExPath,
              <T as Constrain<EqK<U>>>::Lift: ExPath,
              <<T as Constrain<EqK<U>>>::Lift as ExPath>::Lift: ExPath,
              <<<T as Constrain<EqK<U>>>::Lift as ExPath>::Lift as ExPath>::Lift: ExPath,
              <T as Constrain<GeK<U>>>::Lift: ExPath,
              <<T as Constrain<GeK<U>>>::Lift as ExPath>::Lift: ExPath,
              <<<T as Constrain<GeK<U>>>::Lift as ExPath>::Lift as ExPath>::Lift: ExPath,
              <T as Constrain<LtK<U>>>::Lift: ExPath,
    {
        let b = a.ex_path();
        let c = b.ex_path();
        let _ = c.ex_path();
        let _ = a.i(()).ex_path();
        let b = a.i(Even::default()).ex_path();
        let c = b.ex_path();
        let _ = c.ex_path();
        let b = a.i(Odd::default()).ex_path();
        let c = b.ex_path();
        let _ = c.ex_path();
        let b = a.i(EqK {k: (2 as u8).into(), i: ()}).ex_path();
        let c = b.ex_path();
        let _ = c.ex_path();
        let b = a.i(GeK {k: (2 as u8).into(), i: ()}).ex_path();
        let c = b.ex_path();
        let _ = c.ex_path();
        let _ = a.i(LtK {k: (2 as u8).into(), i: ()}).ex_path();
    }

    macro_rules! test_nat (
        ($t:ident) => {{
            type Nat = $t;
            let even: Even<Nat> = Even::default();
            let odd: Odd<Nat> = Odd::default();
            let add_2: AddK<Nat> = AddK {k: 2, i: ()};
            let ge_2: GeK<Nat> = add_2.ex_path();
            let lt_2: LtK<Nat> = LtK {k: 2, i: ()};
            let eq_2: EqK<Nat> = EqK {k: 2, i: ()};
            let if_ge_2_even_odd = If {co: ge_2, tr: even, fa: odd, i: ()};
            let if_ge_2_odd_even = If {co: ge_2, tr: odd, fa: even, i: ()};
            let if_lt_2_even_odd = If {co: lt_2, tr: even, fa: odd, i: ()};
            let if_lt_2_odd_even = If {co: lt_2, tr: odd, fa: even, i: ()};
            let if_ge_2_even_even = If {co: ge_2, tr: even, fa: even, i: ()};
            let if_lt_2_even_even = If {co: lt_2, tr: even, fa: even, i: ()};

            test_nat(add_2);
            test_nat(ge_2);
            test_nat(lt_2);
            test_nat(eq_2);
            test_nat(even);
            test_nat(odd);
            test_nat(if_ge_2_even_odd);
            test_nat(if_ge_2_odd_even);
            test_nat(if_lt_2_even_odd);
            test_nat(if_lt_2_odd_even);
            test_nat(if_ge_2_even_even);
            test_nat(if_lt_2_even_even);
        }};
    );

    #[test]
    fn it_works() {
        let false_1_bool: False1<bool> = False1::default();
        let not: Not = Not::default();
        let id_bool: Id<bool> = Id::default();
        test_bool(false_1_bool);
        test_bool(not);
        test_bool(id_bool);
        test_bool(());

        let and: And = And::default();
        let or: Or = Or::default();
        let eq_bool: Eq<bool> = Eq::default();
        let xor: Xor = Xor::default();
        let nand: Nand = Nand::default();
        let nor: Nor = Nor::default();
        let exc: Exc = Exc::default();
        let nrexc: Nrexc = Nrexc::default();
        let rexc: Rexc = Rexc::default();
        let nexc: Nexc = Nexc::default();
        test_bool_bool(and);
        test_bool_bool(or);
        test_bool_bool(eq_bool);
        test_bool_bool(xor);
        test_bool_bool(nand);
        test_bool_bool(nor);
        test_bool_bool(exc);
        test_bool_bool(nrexc);
        test_bool_bool(rexc);
        test_bool_bool(nexc);

        test_bool_bool_path!(not: not, id_bool: id_bool,
            [and, Or], [or, And], [eq_bool, Xor], [xor, Eq<bool>],
            [exc, Nrexc], [nrexc, Exc], [nexc, Rexc], [rexc, Nexc]);

        test_nat!(u8);
        test_nat!(u16);
        test_nat!(u32);
        test_nat!(u64);

        type Nat = u16;
        let add: Add<Nat> = Add::default();

        let even: Even<Nat> = Even::default();
        let odd: Odd<Nat> = Odd::default();
        let add_2: AddK<Nat> = AddK {k: 2, i: ()};
        let ge_2: GeK<Nat> = add_2.ex_path();

        let _: Eq<bool, _> = add.path(even);
        let _: Xor = add.path(odd);

        assert_eq!(ge_2.k, 2);

        // ∃(>= k) => \(x: bool) = if k == 0 {x} else {true}
        // The existential path alternates in the branches.
        let ifkzxt = ge_2.ex_path();
        let ifkztx = ifkzxt.ex_path();
        let ifkzxt2 = ifkztx.ex_path();
        assert_eq!(ifkzxt, ifkzxt2);

        let a = add.i((even, odd)).ex_path();
        let b = a.ex_path();
        let c = b.ex_path();
        let _ = c.ex_path();
        let a = add.i((odd, even)).ex_path();
        let b = a.ex_path();
        let c = b.ex_path();
        let _ = c.ex_path();
        let a = add.i((even, even)).ex_path();
        let b = a.ex_path();
        let c = b.ex_path();
        let _ = c.ex_path();
        let a = add.i((odd, odd)).ex_path();
        let b = a.ex_path();
        let c = b.ex_path();
        let _ = c.ex_path();

        let _: Eq<bool, (Id<bool>, Not)> = add.i((even, odd)).path(even);
        let _: Eq<bool, (Id<bool>, Id<bool>)> = add.i((even, even)).path(even);
        let _: Eq<bool, (Not, Id<bool>)> = add.i((odd, even)).path(even);
        let _: Eq<bool, (Not, Not)> = add.i((odd, odd)).path(even);
    }
}
