#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn triangle(a: i32, b: i32, c: i32) -> (result: i32)
    requires
        i32::MIN <= a + b <= i32::MAX && i32::MIN <= a + b + c <= i32::MAX,
    ensures
        ((a + b + c == 180) && a > 0 && b > 0 && c > 0) ==> (result == 1),
        ((!((((a + b + c == 180) && a > 0 && b > 0 && c > 0)) as int != 0))) ==> (result == 0),
{
    if (a + b + c == 180) && a > 0 && b > 0 && c > 0 {
        1
    } else {
        0
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn check_validity() {
    let res: i32 = triangle(90, 45, 45);
    assert(res == 1);
}

fn main() {
}

} // verus!
