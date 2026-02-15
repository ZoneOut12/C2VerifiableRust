// #[allow(unused_imports)]
// use vstd::math::*;
// use vstd::prelude::*;
// use vstd::slice::*;
// verus! {

// #[verifier::loop_isolation(false)]
// #[verifier::exec_allows_no_decreases_clause]
// fn add(p: &i32, q: &i32) -> (result: i32)
//     requires
//         true && true,
//         true,
//         ((p)@) + ((q)@) <= i32::MAX,
//         ((p)@) + ((q)@) >= i32::MIN,
//     ensures
//         result == ((p)@) + ((q)@),
// {
//     *p + *q
// }

// fn CheckPre_add(p: &i32, q: &i32)
//     requires
//         ((p)@) + ((q)@) <= i32::MAX,
//         ((p)@) + ((q)@) >= i32::MIN,
// {}

// fn CheckPost_add(p: &i32, q: &i32, result: i32)
//     requires
//         result == ((p)@) + ((q)@),
// {}

// #[verifier::loop_isolation(false)]
// #[verifier::exec_allows_no_decreases_clause]
// fn main() {
//     let a: i32 = 24;
//     let b: i32 = 32;
//     let x: i32;
//     x = add(&a, &b);
//     assert(x == a + b);
//     assert(x == 56);
// }

// fn valid_test_harness_add() {
//     // Test case 1: Valid - positive numbers
//     let a1 = 24; let b1 = 32;
//     CheckPre_add(&a1, &b1);
//     let result1 = 56;
//     CheckPost_add(&a1, &b1, result1);

//     // Test case 2: Valid - negative numbers
//     let a2 = -10; let b2 = -20;
//     CheckPre_add(&a2, &b2);
//     let result2 = -30;
//     CheckPost_add(&a2, &b2, result2);

//     // Test case 3: Valid - mixed signs
//     let a3 = 50; let b3 = -20;
//     CheckPre_add(&a3, &b3);
//     let result3 = 30;
//     CheckPost_add(&a3, &b3, result3);

//     // Test case 4: Valid - with zero
//     let a4 = 100; let b4 = 0;
//     CheckPre_add(&a4, &b4);
//     let result4 = 100;
//     CheckPost_add(&a4, &b4, result4);

//     // Test case 5: Valid - zeros
//     let a5 = 0; let b5 = 0;
//     CheckPre_add(&a5, &b5);
//     let result5 = 0;
//     CheckPost_add(&a5, &b5, result5);

//     // Test case 8: Boundary - sum equals INT_MAX
//     let a8 = i32::MAX; let b8 = 0;
//     CheckPre_add(&a8, &b8);
//     let result8 = i32::MAX;
//     CheckPost_add(&a8, &b8, result8);

//     // Test case 9: Boundary - sum equals INT_MIN
//     let a9 = i32::MIN; let b9 = 0;
//     CheckPre_add(&a9, &b9);
//     let result9 = i32::MIN;
//     CheckPost_add(&a9, &b9, result9);
// }

// fn invalid_test_harness_add() {
//     // Test case 6 (Revised): Invalid - overlapping pointers/alias
//     // In Rust, using references to the same variable is a separation violation
//     let a6 = i32::MIN;
//     let b6 = i32::MIN;
//     CheckPre_add(&a6, &b6);

//     // Test case 7: Invalid - integer overflow (INT_MAX + 1)
//     let a7 = i32::MAX;
//     let b7 = 1;
//     CheckPre_add(&a7, &b7);
// }

// } // verus!


// RAC
fn add(p: &i32, q: &i32) -> i32
{
    *p + *q
}

fn main() {
    let a: i32 = 24;
    let b: i32 = 32;
    let x: i32;
    x = add(&a, &b);
    assert!(x == a + b);
    assert!(x == 56);
}