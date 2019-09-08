/*

This example shows how to use the library with Boolean algebra.

A function is constrained by the `.i` method:

    and.i((id, id))     // Constrains both inputs to `true`
    and.i((not, not))   // Constrains both inputs to `false`
    and.i(((), ()))     // Constrains both inputs to `false | true`.
    and.i((fa, fa))     // Constrains both inputs to `` (none).

The last version does not implement a trait,
since it is required that there exists some input for it to make sense.

Notice that constraining the input to a unique value makes it
possible to check a normal path for a concrete case.

This means that even checking existential paths for constraints
is only accurate up to output permutations, it is possible to quantify
over checks of unique constraints to get full accuracy.

*/

extern crate path_semantics_std;

use path_semantics_std::*;

fn main() {
    let and: And = And::default();
    let or: Or = Or::default();
    let not: Not = Not::default();
    let id: Id<bool> = Id::default();
    let fa: False1<bool> = False1::default();

    // `and[not] <=> or`
    assert_eq!(and.path(not), or);
    // `or[not] <=> and`
    assert_eq!(or.path(not), and);

    // `and{(= false), (= false)}[not] => or{(= true), (= true)}`.
    assert_eq!(and.i((not, not)).path(not), or.i((id, id)));
    // `and{(= true), (= true)}[not] => or{(= false), (= false)}`.
    assert_eq!(and.i((id, id)).path(not), or.i((not, not)));
    // `and{(= false), _}[not] => or{(= true), _}`.
    assert_eq!(and.i((not, ())).path(not), or.i((id, ())));
    // `and{_, (= false)}[not] => or{_, (= true)}`.
    assert_eq!(and.i(((), not)).path(not), or.i(((), id)));
    // `and{_, _}[not] => or{_, _}`
    assert_eq!(and.i(((), ())).path(not), or.i(((), ())));
}
