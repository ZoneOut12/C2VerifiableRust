#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn validts(a: i32, b: i32, c: i32) -> (result: i32)
    requires
        a > 0 && b > 0 && c > 0,
        a + b + c <= i32::MAX,
    ensures
        ((a + b > c) && (a + c > b) && (b + c > a)) ==> (result == 1),
        ((!((((a + b > c) && (a + c > b) && (b + c > a))) as int != 0))) ==> (result == 0),
{
    let mut valid: i32 = 0;
    if (a + b > c) && (a + c > b) && (b + c > a) {
        valid = 1;
    } else {
        valid = 0;
    }
    valid
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn test() {
    let valid: i32 = validts(2, 3, 4);
    assert(valid == 1);
}

fn main() {
}

} // verus!
