#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn add(x: i32, y: i32) -> (result: i32)
    requires
        x + y <= i32::MAX,
        x + y >= i32::MIN,
    ensures
        result == x + y,
{
    x + y
}

fn CheckPre_add(x: i32, y: i32)
    requires
        x + y <= i32::MAX,
        x + y >= i32::MIN,
{}

fn CheckPost_add(x: i32, y: i32, result: i32)
    requires
        result == x + y,
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo() {
    let a: i32 = add(1, 43);
}

fn main() {
}

fn valid_test_harness_add() {
    // Test case 1: Valid - normal case from foo
    let x1 = 1; let y1 = 43;
    CheckPre_add(x1, y1);
    let result1 = 44;
    CheckPost_add(x1, y1, result1);

    // Test case 2: Valid - small positive numbers
    let x2 = 10; let y2 = 20;
    CheckPre_add(x2, y2);
    let result2 = 30;
    CheckPost_add(x2, y2, result2);

    // Test case 3: Valid - zeros
    let x3 = 0; let y3 = 0;
    CheckPre_add(x3, y3);
    let result3 = 0;
    CheckPost_add(x3, y3, result3);

    // Test case 4: Valid - negative and positive
    let x4 = -5; let y4 = 3;
    CheckPre_add(x4, y4);
    let result4 = -2;
    CheckPost_add(x4, y4, result4);

    // Test case 5: Valid - sum at INT_MAX
    let x5 = i32::MAX - 1; let y5 = 1;
    CheckPre_add(x5, y5);
    let result5 = i32::MAX;
    CheckPost_add(x5, y5, result5);

    // Test case 8: Boundary - sum equals INT_MAX
    let x8 = i32::MAX; let y8 = 0;
    CheckPre_add(x8, y8);
    let result8 = i32::MAX;
    CheckPost_add(x8, y8, result8);

    // Test case 9: Boundary - sum equals INT_MIN
    let x9 = i32::MIN; let y9 = 0;
    CheckPre_add(x9, y9);
    let result9 = i32::MIN;
    CheckPost_add(x9, y9, result9);
}

fn invalid_test_harness_add() {
    // Test case 6: Invalid - sum exceeds INT_MAX
    let x6 = 2147483647; // i32::MAX
    let y6 = 1;
    CheckPre_add(x6, y6);

    // Test case 7: Invalid - sum below INT_MIN
    let x7 = -2147483648; // i32::MIN
    let y7 = -1;
    CheckPre_add(x7, y7);
}

} // verus!
