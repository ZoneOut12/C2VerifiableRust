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

fn CheckPost_max(x0: i32, x1: i32, result: i32)
    requires
        (((result >= x0) && (result >= x1)) && ((result == x0) || (result == x1))),
{}

fn main() {
}

fn valid_test_harness() {
    max(5, 3);
    let result = 5;
    CheckPost_max(5, 3, result);

    max(-5, 10);
    let result = 10;
    CheckPost_max(-5, 10, result);

    max(0, 0);
    let result = 0;
    CheckPost_max(0, 0, result);

    max(i32::MIN, i32::MAX);
    let result = i32::MAX;
    CheckPost_max(i32::MIN, i32::MAX, result);

    max(42, -42);
    let result = 42;
    CheckPost_max(42, -42, result);

    max(i32::MAX, i32::MAX);
    let result = i32::MAX;
    CheckPost_max(i32::MAX, i32::MAX, result);

    max(i32::MIN, i32::MIN);
    let result = i32::MIN;
    CheckPost_max(i32::MIN, i32::MIN, result);
}

} // verus!
