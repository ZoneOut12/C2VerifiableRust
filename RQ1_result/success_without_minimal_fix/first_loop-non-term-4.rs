#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut i: i32 = 0;
    let mut h: i32 = 42;

    while i < 29
        invariant
            0 <= i <= 29,
        decreases 30 - i,
    {
        i += 1;
    }

    if i < 30 {
        i += 1;

        if i == 30 {
            i = 42;
            h = 84;
        }
    }
    assert(i == 42);
    assert(h == 84);
}

} // verus!
