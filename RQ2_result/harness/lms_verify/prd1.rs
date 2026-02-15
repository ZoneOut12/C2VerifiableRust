#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn is_pos(x: i32) -> bool {
    x > 0
}

pub open spec fn is_nat(x: i32) -> bool {
    x >= 0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn minus1(x: i32) -> (result: i32)
    requires
        (is_pos(x as i32)),
    ensures
        (is_nat(result as i32)),
{
    x - 1
}

fn CheckPre_minus1(x: i32)
    requires
        (is_pos(x as i32)),
{}

fn CheckPost_minus1(x: i32, result: i32)
    requires
        (is_nat(result as i32)),
{}

fn main() {
}

fn valid_test_harness_minus1() {
    // Test case 1: Valid input x=2
    let x1 = 2;
    CheckPre_minus1(x1);
    let result1 = 1; // Hardcoded Expected: 2 - 1
    CheckPost_minus1(x1, result1);

    // Test case 2: Valid input x=5
    let x2 = 5;
    CheckPre_minus1(x2);
    let result2 = 4; // Hardcoded Expected: 5 - 1
    CheckPost_minus1(x2, result2);

    // Test case 3: Valid input x=10
    let x3 = 10;
    CheckPre_minus1(x3);
    let result3 = 9; // Hardcoded Expected: 10 - 1
    CheckPost_minus1(x3, result3);

    // Test case 4: Valid input x=42
    let x4 = 42;
    CheckPre_minus1(x4);
    let result4 = 41; // Hardcoded Expected: 42 - 1
    CheckPost_minus1(x4, result4);

    // Test case 5: Valid input x=100
    let x5 = 100;
    CheckPre_minus1(x5);
    let result5 = 99; // Hardcoded Expected: 100 - 1
    CheckPost_minus1(x5, result5);

    // Test case 8: Boundary case x=1
    let x8 = 1;
    CheckPre_minus1(x8);
    let result8 = 0; // Hardcoded Expected: 1 - 1
    CheckPost_minus1(x8, result8);

    // Test case 9: Boundary case x=2 (Duplicate of case 1 logic)
    let x9 = 2;
    CheckPre_minus1(x9);
    let result9 = 1;
    CheckPost_minus1(x9, result9);
}

fn invalid_test_harness_minus1() {
    // Test case 6: Invalid input x=0
    // Violates: requires is_pos(x6)
    CheckPre_minus1(0);

    // Test case 7: Invalid input x=-5
    // Violates: requires is_pos(x6)
    CheckPre_minus1(-5);
}

} // verus!
