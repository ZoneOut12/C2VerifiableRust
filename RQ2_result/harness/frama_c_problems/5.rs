#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn fun(x: i32, y: i32, r: &mut i32) -> (result: i32)
    requires
        x >= y && x > 0 && y > 0,
        true,
    ensures
        ((r)@) < y,
        x == result * y + ((r)@),
{
    *r = x;
    let mut d: i32 = 0;
    while *r >= y
        invariant
            ((r)@) == x - y * d,
        decreases ((r)@),
    {
        *r = *r - y;
        d = d + 1;
    }
    d
}

fn CheckPre_fun(x: i32, y: i32, r: &i32)
    requires
        x >= y && x > 0 && y > 0,
        true,
{}

fn CheckPost_fun(x: i32, y: i32, r: &i32, result: i32)
    requires
        ((r)@) < y,
        x == result * y + ((r)@),
{}


fn main() {
}

fn valid_test_harness_fun() {
    // Test case 1: 6 / 4 = 1 ... 2
    let r1 = 2; // Remainder
    CheckPre_fun(6, 4, &r1);
    let result1 = 1; // Quotient
    CheckPost_fun(6, 4, &r1, result1);

    // Test case 2: 10 / 5 = 2 ... 0
    let r2 = 0;
    CheckPre_fun(10, 5, &r2);
    let result2 = 2;
    CheckPost_fun(10, 5, &r2, result2);

    // Test case 3: 3 / 3 = 1 ... 0
    let r3 = 0;
    CheckPre_fun(3, 3, &r3);
    let result3 = 1;
    CheckPost_fun(3, 3, &r3, result3);

    // Test case 4: 2 / 1 = 2 ... 0
    let r4 = 0;
    CheckPre_fun(2, 1, &r4);
    let result4 = 2;
    CheckPost_fun(2, 1, &r4, result4);

    // Test case 5: 1 / 1 = 1 ... 0
    let r5 = 0;
    CheckPre_fun(1, 1, &r5);
    let result5 = 1;
    CheckPost_fun(1, 1, &r5, result5);

    // Test case 8: 1 / 1 redundant logic
    let r8 = 0;
    CheckPre_fun(1, 1, &r8);
    let result8 = 1;
    CheckPost_fun(1, 1, &r8, result8);

    // Test case 9: 2 / 1 redundant logic
    let r9 = 0;
    CheckPre_fun(2, 1, &r9);
    let result9 = 2;
    CheckPost_fun(2, 1, &r9, result9);
}

fn invalid_test_harness_fun() {
    // Test case 6: Invalid - x < y (Violation: x >= y)
    let r6 = 0;
    CheckPre_fun(3, 5, &r6);

    // Test case 7: Violation of numerical constraints
    CheckPre_fun(-1, 0, &r6);
}

} // verus!


// RAC
// fn fun(x: i32, y: i32, r: &mut i32) -> i32
// {
//     *r = x;
//     let mut d: i32 = 0;
//     while *r >= y
//     {
//         let old_measure = *r;
//         assert!(*r == x - y * d);
//         *r = *r - y;
//         d = d + 1;
//         assert!(old_measure > *r);
//     }
//     assert!(*r == x - y * d);
//     d
// }

// fn main() {
//     valid_test_harness_fun();
// }

// fn valid_test_harness_fun() {
//     // Test case 1: 6 / 4 = 1 ... 2
//     let mut r1 = 2;
//     fun(6, 4, &mut r1);

//     // Test case 2: 10 / 5 = 2 ... 0
//     let mut r2 = 0;
//     fun(10, 5, &mut r2);

//     // Test case 3: 3 / 3 = 1 ... 0
//     let mut r3 = 0;
//     fun(3, 3, &mut r3);

//     // Test case 4: 2 / 1 = 2 ... 0
//     let mut r4 = 0;
//     fun(2, 1, &mut r4);

//     // Test case 5: 1 / 1 = 1 ... 0
//     let mut r5 = 0;
//     fun(1, 1, &mut r5);

//     // Test case 8: 1 / 1 redundant logic
//     let mut r8 = 0;
//     fun(1, 1, &mut r8);

//     // Test case 9: 2 / 1 redundant logic
//     let mut r9 = 0;
//     fun(2, 1, &mut r9);
// }