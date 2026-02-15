#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max(x: i32, y: i32) -> (result: i32)
    ensures
        result >= x && result >= y,
        result == x || result == y,
{
    if x > y {
        x
    } else {
        y
    }
}

fn CheckPost_max(x: i32, y: i32, result: i32)
    requires
        result >= x && result >= y,
        result == x || result == y,
{}

fn main() {
}

fn valid_test_harness() {
    // Test case 1: x greater than y
    max(5, 3);
    let result = 5;
    CheckPost_max(5, 3, result);

    // Test case 2: y greater than x
    max(-2, 3);
    let result = 3;
    CheckPost_max(-2, 3, result);

    // Test case 3: x is zero
    max(0, -5);
    let result = 0;
    CheckPost_max(0, -5, result);

    // Test case 4: both negative
    max(-5, -3);
    let result = -3;
    CheckPost_max(-5, -3, result);

    // Test case 5: large x
    max(42, 10);
    let result = 42;
    CheckPost_max(42, 10, result);

    // Test case 6: boundary - equal positive
    max(10, 10);
    let result = 10;
    CheckPost_max(10, 10, result);

    // Test case 7: boundary - equal negative
    max(-5, -5);
    let result = -5;
    CheckPost_max(-5, -5, result);
}

} // verus!
