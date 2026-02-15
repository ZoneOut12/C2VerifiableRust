#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max(x: i32, y: i32) -> (result: i32)
    ensures
        result == x || result == y,
        result >= x && result >= y,
{
    if x >= y {
        return x;
    }
    return y;
}

fn CheckPost_max(x: i32, y: i32, result: i32)
    requires
        result == x || result == y,
        result >= x && result >= y,
{}

fn main() {
}

fn valid_test_harness_max() {
    // Test case 1: Valid - x greater than y
    let x1 = 5;
    let y1 = 3;
    let result1 = 5;
    CheckPost_max(x1, y1, result1);

    // Test case 2: Valid - y greater than x
    let x2 = 2;
    let y2 = 4;
    let result2 = 4;
    CheckPost_max(x2, y2, result2);

    // Test case 3: Valid - x equals y
    let x3 = 7;
    let y3 = 7;
    let result3 = 7;
    CheckPost_max(x3, y3, result3);

    // Test case 4: Valid - x is zero, y is negative
    let x4 = 0;
    let y4 = -5;
    let result4 = 0;
    CheckPost_max(x4, y4, result4);

    // Test case 5: Valid - both negative, x greater
    let x5 = -1;
    let y5 = -3;
    let result5 = -1;
    CheckPost_max(x5, y5, result5);

    // Test case 6: Boundary - maximum integer values
    let x6 = i32::MAX;
    let y6 = i32::MAX;
    let result6 = i32::MAX;
    CheckPost_max(x6, y6, result6);

    // Test case 7: Boundary - minimum integer values
    let x7 = i32::MIN;
    let y7 = i32::MIN;
    let result7 = i32::MIN;
    CheckPost_max(x7, y7, result7);
}

} // verus!
