#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn add(a: &i32, b: &i32, r: &i32) -> (result: i32)
    requires
        ((a)@) + ((b)@) <= i32::MAX,
        ((a)@) + ((b)@) >= i32::MIN,
        ((a)@) + ((b)@) + ((r)@) <= i32::MAX,
        ((a)@) + ((b)@) + ((r)@) >= i32::MIN,
    ensures
        result == ((a)@) + ((b)@) + ((r)@),
{
    *a + *b + *r
}

fn CheckPre_add(a: &i32, b: &i32, r: &i32)
    requires
        ((a)@) + ((b)@) <= i32::MAX,
        ((a)@) + ((b)@) >= i32::MIN,
        ((a)@) + ((b)@) + ((r)@) <= i32::MAX,
        ((a)@) + ((b)@) + ((r)@) >= i32::MIN,
{}

fn CheckPost_add(a: &i32, b: &i32, r: &i32, result: i32)
    requires
        result == ((a)@) + ((b)@) + ((r)@),
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut a: i32 = 24;
    let mut b: i32 = 32;
    let mut r: i32 = 12;
    let mut x: i32;
    x = add(&a, &b, &r);
    assert(x == a + b + r);
    assert(x == 68);
}

fn valid_test_harness_add() {
    // Test case 1: Valid - normal case
    let a1 = 24; let b1 = 32; let r1 = 12;
    CheckPre_add(&a1, &b1, &r1);
    let result1 = 68;
    CheckPost_add(&a1, &b1, &r1, result1);

    // Test case 2: Valid - sum a+b is INT_MAX-1
    let a2 = i32::MAX - 2; let b2 = 1; let r2 = 1;
    CheckPre_add(&a2, &b2, &r2);
    let result2 = i32::MAX;
    CheckPost_add(&a2, &b2, &r2, result2);

    // Test case 3: Valid - negative values
    let a3 = -10; let b3 = -20; let r3 = -30;
    CheckPre_add(&a3, &b3, &r3);
    let result3 = -60;
    CheckPost_add(&a3, &b3, &r3, result3);

    // Test case 4: Valid - all zeros
    let a4 = 0; let b4 = 0; let r4 = 0;
    CheckPre_add(&a4, &b4, &r4);
    let result4 = 0;
    CheckPost_add(&a4, &b4, &r4, result4);

    // Test case 5: Valid - sum a+b is INT_MIN
    let a5 = -1073741824; let b5 = -1073741824; let r5 = 1;
    CheckPre_add(&a5, &b5, &r5);
    let result5 = -2147483647;
    CheckPost_add(&a5, &b5, &r5, result5);

    // Test case 6: Boundary - sum is INT_MAX
    let a6 = i32::MAX; let b6 = 0; let r6 = 0;
    CheckPre_add(&a6, &b6, &r6);
    let result6 = i32::MAX;
    CheckPost_add(&a6, &b6, &r6, result6);

    // Test case 7: Boundary - sum is INT_MIN
    let a7 = i32::MIN; let b7 = 0; let r7 = 0;
    CheckPre_add(&a7, &b7, &r7);
    let result7 = i32::MIN;
    CheckPost_add(&a7, &b7, &r7, result7);
}

fn invalid_test_harness_add() {
    let a8 = i32::MAX - 1;
    let b8 = i32::MAX - 1;
    let r8 = i32::MAX - 1;
    CheckPre_add(&a8, &b8, &r8);

    let a9 = i32::MAX;
    let b9 = 1;
    let r9 = 0;
    CheckPre_add(&a9, &b9, &r9);
}

} // verus!


// RAC
// fn add(a: &i32, b: &i32, r: &i32) -> i32
// {
//     *a + *b + *r
// }

// fn main() {
//     let mut a: i32 = 24;
//     let mut b: i32 = 32;
//     let mut r: i32 = 12;
//     let mut x: i32;
//     x = add(&a, &b, &r);
//     assert!(x == a + b + r);
//     assert!(x == 68);
// }