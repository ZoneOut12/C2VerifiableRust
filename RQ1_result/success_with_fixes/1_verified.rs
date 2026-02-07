#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut x: i64 = 1;
    let mut y: i64 = 0;

    while y < 100000
        invariant
            y <= x,
            y <= 100000,
            x == ((y - 1) * y) / 2 + 1,
            1 <= x,
            0 <= y,
        decreases 100000 - y,
    {
        x = x + y;
        y = y + 1;
    }
    assert((x >= y));
}

} // verus!
