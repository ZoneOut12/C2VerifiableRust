#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn inc(x: i32) -> (result: i32)
    requires
        x < i32::MAX,
    ensures
        result > x,
{
    x + 1
}

fn CheckPost_inc(x: i32, result: i32)
    requires 
        result > x,
{}

fn main() {
}

fn valid_test_harness() {
    // Test case 1: zero
    inc(0);
    let result = 1;
    CheckPost_inc(0, result);

    // Test case 2: positive number
    inc(42);
    let result = 43;
    CheckPost_inc(42, result);

    // Test case 3: negative number
    inc(-10);
    let result = -9;
    CheckPost_inc(-10, result);

    // Test case 4: mid-range positive
    inc(1000);
    let result = 1001;
    CheckPost_inc(1000, result);

    // Test case 5: near upper bound (INT_MAX - 2)
    inc(i32::MAX - 2);
    let result = i32::MAX - 1;
    CheckPost_inc(i32::MAX - 2, result);

    // Test case 6: boundary (INT_MAX - 1)
    inc(i32::MAX - 1);
    let result = i32::MAX;
    CheckPost_inc(i32::MAX - 1, result);

    // Test case 7: minimum integer value (INT_MIN)
    inc(i32::MIN);
    let result = i32::MIN + 1;
    CheckPost_inc(i32::MIN, result);
}

fn invalid_test_harness_1() {
    inc(i32::MAX);
}

} // verus!
