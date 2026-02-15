#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut i: i32 = 0;

    while i < 30
        invariant
            0 <= i <= 30,
        decreases 30 - i,
    {
        i += 1;
    }
    assert(i == 30);
}

} // verus!
