#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn func(c: i32) -> (result: i32)
    requires
        c > 0,
    ensures
        result == c,
{
    let mut x: i32 = c;
    let mut y: i32 = 0;
    while x > 0
        invariant
            c == x + y && x >= 0,
        decreases x,
    {
        x = x - 1;
        y = y + 1;
    }
    y
}

fn CheckPre_func(c: i32)
    requires
        c > 0,
{}

fn CheckPost_func(c: i32, result: i32)
    requires
        result == c,
{}

fn main() {
}

fn valid_test_harness_func() {
    // Test case 1: Valid - minimal allowed value
    let c1 = 1;
    CheckPre_func(c1);
    let result1 = 1; // Expected: y == c
    CheckPost_func(c1, result1);

    // Test case 2: Valid - medium value
    let c2 = 5;
    CheckPre_func(c2);
    let result2 = 5;
    CheckPost_func(c2, result2);

    // Test case 3: Valid - another typical value
    let c3 = 10;
    CheckPre_func(c3);
    let result3 = 10;
    CheckPost_func(c3, result3);

    // Test case 4: Valid - larger value
    let c4 = 100;
    CheckPre_func(c4);
    let result4 = 100;
    CheckPost_func(c4, result4);

    // Test case 5: Valid - large value
    let c5 = 1000;
    CheckPre_func(c5);
    let result5 = 1000;
    CheckPost_func(c5, result5);

    // Test case 6: Boundary - minimal allowed value
    let c6 = 1;
    CheckPre_func(c6);
    let result6 = 1;
    CheckPost_func(c6, result6);

    // Test case 7: Boundary - loop execution test (c=2)
    let c7 = 2;
    CheckPre_func(c7);
    let result7 = 2;
    CheckPost_func(c7, result7);
}

fn invalid_test_harness_func() {
    // Test case 8: Invalid - zero input (Violation: requires c > 0)
    let c8 = 0;
    CheckPre_func(c8);

    // Test case 9: Invalid - negative input (Violation: requires c > 0)
    let c9 = -5;
    CheckPre_func(c9);
}

} // verus!

// RAC
// fn func(c: i32) -> i32
// {
//     let mut x: i32 = c;
//     let mut y: i32 = 0;
//     while x > 0
//     {
//         let old_measure = x;
//         assert!(c == x + y && x >= 0);
//         x = x - 1;
//         y = y + 1;
//         assert!(old_measure > x);
//     }
//     assert!(c == x + y && x >= 0);
//     y
// }

// fn main() {
//     valid_test_harness_func();
// }

// fn valid_test_harness_func() {
//     // Test case 1: Valid - minimal allowed value
//     let c1 = 1;
//     func(c1);

//     // Test case 2: Valid - medium value
//     let c2 = 5;
//     func(c2);

//     // Test case 3: Valid - another typical value
//     let c3 = 10;
//     func(c3);

//     // Test case 4: Valid - larger value
//     let c4 = 100;
//     func(c4);

//     // Test case 5: Valid - large value
//     let c5 = 1000;
//     func(c5);

//     // Test case 6: Boundary - minimal allowed value
//     let c6 = 1;
//     func(c6);

//     // Test case 7: Boundary - loop execution test (c=2)
//     let c7 = 2;
//     func(c7);
// }
