#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn reset_1st_if_2nd_is_true(a: &mut i32, b: &i32)
    ensures
        (((b)@)) as int != 0 ==> (((a)@) == 0) as int != 0,
        ((!((((b)@)) as int != 0))) as int != 0 ==> (((a)@) == ((old(a))@)) as int != 0,
        ((b)@) == ((b)@),
{
    if *b != 0 {
        *a = 0;
    }
}

fn CheckPost_reset_1st_if_2nd_is_true(old_a: &i32, a: &i32, b: &i32)
    requires
        (((b)@)) as int != 0 ==> (((a)@) == 0) as int != 0,
        ((!((((b)@)) as int != 0))) as int != 0 ==> (((a)@) == ((old_a)@)) as int != 0,
        ((b)@) == ((b)@),
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut a: i32 = 5;
    let x: i32 = 0;
    reset_1st_if_2nd_is_true(&mut a, &x);
    assert(a == 5);
    assert(x == 0);

    let b: i32 = 1;
    reset_1st_if_2nd_is_true(&mut a, &b);
    assert(a == 0);
    assert(b == 1);
}

fn valid_test_harness_reset() {
    // Case 1: Standard True - a is reset
    let a1 = 5;
    let b1 = 1;
    let (new_a1, new_b1) = (0, 1);
    CheckPost_reset_1st_if_2nd_is_true(&a1, &new_a1, &new_b1);

    // Case 2: Standard False - a remains unchanged
    let a2 = 5;
    let b2 = 0;
    let (new_a2, new_b2) = (5, 0);
    CheckPost_reset_1st_if_2nd_is_true(&a2, &new_a2, &new_b2);

    // Case 3: Negative True - -1 is true
    let a3 = 10;
    let b3 = -1;
    let (new_a3, new_b3) = (0, -1);
    CheckPost_reset_1st_if_2nd_is_true(&a3, &new_a3, &new_b3);

    // Case 4: Large True - b is i32::MAX
    let a4 = 100;
    let b4 = i32::MAX;
    let (new_a4, new_b4) = (0, i32::MAX);
    CheckPost_reset_1st_if_2nd_is_true(&a4, &new_a4, &new_b4);

    // Case 5: Already Zero - b is true
    let a5 = 0;
    let b5 = 42;
    let (new_a5, new_b5) = (0, 42);
    CheckPost_reset_1st_if_2nd_is_true(&a5, &new_a5, &new_b5);

    // Case 6: Multiple calls - persistence
    let a6 = 9;
    let b6_1 = 1;
    let b6_2 = 0;
    let res_a_step1 = 0; 
    CheckPost_reset_1st_if_2nd_is_true(&a6, &res_a_step1, &b6_1);

    // Case 7: Boundary - b is i32::MIN (True)
    let a7 = 123;
    let b7 = i32::MIN;
    let (new_a7, new_b7) = (0, i32::MIN);
    CheckPost_reset_1st_if_2nd_is_true(&a7, &new_a7, &new_b7);
}


} // verus!

// RAC
// fn reset_1st_if_2nd_is_true(a: &mut i32, b: &i32)
// {
//     if *b != 0 {
//         *a = 0;
//     }
// }

// fn main() {
//     let mut a: i32 = 5;
//     let x: i32 = 0;
//     reset_1st_if_2nd_is_true(&mut a, &x);
//     assert!(a == 5);
//     assert!(x == 0);

//     let b: i32 = 1;
//     reset_1st_if_2nd_is_true(&mut a, &b);
//     assert!(a == 0);
//     assert!(b == 1);
// }

// fn invalid_test_harness_reset() {
//     // Case 8: NULL pointer simulation
//     // reset_1st_if_2nd_is_true(None, &1);

//     // Case 9: Non-separated pointers simulation
//     // let x = 10;
//     // reset_1st_if_2nd_is_true(&x, &x);
// }