#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut x: i32 = 1;
    let mut y: i32 = 0;

    while x <= 10
        invariant
            y <= 10,
            x >= 1 && x <= 11,
            x <= 11,
            1 <= x,
            0 <= y,
        decreases 10 - x + u128::MAX, //2d
    {
        y = 10 - x;
        x = x + 1;
    }

    assert(y >= 0);
}

} // verus!
