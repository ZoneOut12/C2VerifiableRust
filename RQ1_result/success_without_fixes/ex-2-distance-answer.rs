#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn distance(a: i32, b: i32) -> (result: i32)
    requires
        (a < b) as int != 0 ==> (b - a <= i32::MAX) as int != 0,
        (b <= a) as int != 0 ==> (a - b <= i32::MAX) as int != 0,
    ensures
        (a < b) as int != 0 ==> (a + result == b) as int != 0,
        (b <= a) as int != 0 ==> (a - result == b) as int != 0,
{
    if a < b {
        return b - a;
    } else {
        return a - b;
    }
}

fn main() {
}

} // verus!
