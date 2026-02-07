#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max(x0: i32, x1: i32) -> (result: i32)
    ensures
        (((result >= x0) && (result >= x1)) && ((result == x0) || (result == x1))),
{
    let x3: i32 = (x0 > x1) as i32;
    let x4: i32;
    if x3 != 0 {
        x4 = x0;
    } else {
        x4 = x1;
    }
    x4
}

fn main() {
}

} // verus!
