#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn diff(x: i32, y: i32) -> (result: i32)
    requires
        i32::MIN <= x - y <= i32::MAX,
    ensures
        y == x - result,
{
    x - y
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let t: i32 = diff(10, 5);
    assert(t == 5);
}

fn CheckPre_diff(x: i32, y: i32)
    requires
        i32::MIN <= x - y <= i32::MAX,
{}

fn CheckPost_diff(x: i32, y: i32, result: i32)
    requires
        y == x - result,
{}

fn valid_test_harness_diff() {
    // Test case 1: Valid - normal subtraction
    let x1 = 10; let y1 = 5;
    CheckPre_diff(x1, y1);
    let result1 = 5;
    CheckPost_diff(x1, y1, result1);

    // Test case 2: Valid - negative result
    let x2 = 5; let y2 = 10;
    CheckPre_diff(x2, y2);
    let result2 = -5;
    CheckPost_diff(x2, y2, result2);

    // Test case 3: Valid - zero minus negative
    let x3 = 0; let y3 = -5;
    CheckPre_diff(x3, y3);
    let result3 = 5;
    CheckPost_diff(x3, y3, result3);

    // Test case 4: Valid - x near max
    let x4 = i32::MAX - 1; let y4 = 0;
    CheckPre_diff(x4, y4);
    let result4 = i32::MAX - 1;
    CheckPost_diff(x4, y4, result4);

    // Test case 5: Valid - x near min
    let x5 = i32::MIN + 1; let y5 = 0;
    CheckPre_diff(x5, y5);
    let result5 = i32::MIN + 1;
    CheckPost_diff(x5, y5, result5);

    // Test case 6: Boundary - x at max
    let x6 = i32::MAX; let y6 = 0;
    CheckPre_diff(x6, y6);
    let result6 = i32::MAX;
    CheckPost_diff(x6, y6, result6);

    // Test case 7: Boundary - x at min
    let x7 = i32::MIN; let y7 = 0;
    CheckPre_diff(x7, y7);
    let result7 = i32::MIN;
    CheckPost_diff(x7, y7, result7);
}

fn invalid_test_harness_diff() {
    // Test case 8: Invalid - underflow (INT_MIN - 1)
    let x8 = i32::MIN;
    let y8 = 1;
    CheckPre_diff(x8, y8);

    // Test case 9: Invalid - overflow (INT_MAX - (-1))
    let x9 = i32::MAX;
    let y9 = -1;
    CheckPre_diff(x9, y9);
}

} // verus!


// RAC
// fn diff(x: i32, y: i32) -> i32
// {
//     x - y
// }

// fn main() {
//     let t: i32 = diff(10, 5);
//     assert!(t == 5);
// }