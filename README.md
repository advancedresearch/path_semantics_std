# path_semantics_std
A Rust type checked implementation of the standard dictionary of path semantics using constrained functions

*Notice! This library is in early stage of development and might contain bugs and missing features!*

### What is path semantics?

A brief introduction is given here, since most people do not know what it is.  
For more information about path semantics, click [here](https://github.com/advancedresearch/path_semantics).

Path semantics is an attempt to make deep ideas in mathematics more accessible and theorem proving more understandable for programmers.
It is an extension and unification of [dependently types](https://en.wikipedia.org/wiki/Dependent_type) and [guarded commands](https://en.wikipedia.org/wiki/Guarded_Command_Language), that are used today to reason about and verify software.
The major difference from existing work is that path semantics is very high level (more expressive) and allows arbitrary constraints and properties defined by functions.
This makes path semantics in general undecidable, but it has rules that allows checking for consistency for specific problems,
plus the strict concept of function identity that is used when extending the theory to new domains.

The syntax and notation of path semantics is designed to be concise and easily adapted to source code.

- `f{g}` means "constrain `f : A -> B` with `g : A -> bool`".
- `∀f` means "get the constraint of input of `f`".
- Existential path: `∃f : B -> bool` means "what does `f : A -> B` outputs? This depends on the constraint.
- Path: `f[g] <=> h` means "the property `g : A -> B` of `f : A -> A` is predicted by `h : B -> B`.
- Composition: `g . f` outputs `∃g{∃f}`.
- Sub-type: `x : [g] a` where `g : X -> A`, is consistent if `a : [∃g] true`.
- Naming of functions: `false_1, not, id, true_1: bool -> bool` (`id` is generic `A -> A`).
- Surjective xor non-surjective: All "normal" functions has `∃∃f => {id, true_1}`.
- Reduction of proof: `a : [f] b ∧ [g] c` is equal to `a : [f{[g] c}] b` or `a : [g{[f] b}] c`.
- Transform to equations: `f[g] <=> h` gives `g(f(a, b)) = h(g(a), g(b))` (example is for binary functions).
- Propagation of constraints to paths: Used for complain-when-wrong type checking.
- Probabilistic existential path: Like existential path, but for probability theory.
- Probabilistic path: A way to predict properties of output probabilistically from properties of input.

The theory of path semantics reveals that functions are related to each other in a natural occuring space called
"path semantical space", which precisely defines the identity of all functions.
Because the space is organized in a way closely related to the concept of prediction,
the research has lot of overlap with artificial intelligence and machine learning.
Path semantics is a field that studies how this space is organized and higher order algorithms for extracting
and applying knowledge related to perfect and probabilistic prediction.
It is not so much about finding solutions to a single problem, but for studying and understanding higher order reasoning to solve large classes of problems.

### Features

All objects in this library are higher order representations of constrained functions.
This means they do not "compute" but merely construct types of each other, in a way that Rust can type check.

- `Constrain` trait (type `.i(<constrain>)`, `.i_force` skips existential path check)
- `ExPath` trait (type `.ex_path()`)
- `Path` trait (type `.path()`, `.path_force` skips existential path check)
- Complete Boolean algebra (all paths checked with all constraints)
- Some work on natural numbers

One problem is combinatorial explosion because of the complexity of functional spaces.
To work around this issue, there are some tricks applied to reduce the number of building blocks,
such as using `If` and `IfK` for many non-trivial functions.

- `If` has a condition that depends on the argument that is dependend on in the branches
- `IfK` has a condition that is decided at higher order, and therefore not depended on in the branches

The `()` type is used instead of a `True1` because this looks nicer in Rust.

### Future Goals

In the short term this library is intended for research only,
but if it turns out to be useful for theorem proving, the goal is to develop
enough functionality to use it as a core with an ecosystem for domain specific theories.

- Rust's unsigned integer types (u8, u16, u32, u64) for unary and binary operators
- Rust's signed integer types (i8, i16, i32, i64) for unary and binary operators
- Rust's float types
- Vectors
- Complex numbers
- Matrices
