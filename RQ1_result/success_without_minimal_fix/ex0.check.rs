#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn inc(x0: i32) -> (result: i32)
    requires
        (x0 < i32::MAX),
    ensures
        (result > x0),
{
    let x2: i32 = x0 + 1;
    x2
}

fn main() {
}

} // verus!
