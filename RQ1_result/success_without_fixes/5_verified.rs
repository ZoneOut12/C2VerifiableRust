#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut x: i32 = 0;
    let mut size: i32 = 0;
    let mut y: i32 = 0;
    let mut z: i32 = 0;

    while x < size
        invariant
            z >= y || x == 0,
            0 <= x,
        decreases size - x,
    {
        x += 1;
        if z <= y {
            y = z;
        }
    }

    if size > 0 {
        assert(z >= y);
    }
}

} // verus!
