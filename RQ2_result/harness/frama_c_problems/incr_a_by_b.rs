#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn incr_a_by_b(a: &mut i32, b: &i32) -> (result: i32)
    requires
        i32::MIN <= ((old(a))@) + ((b)@) <= i32::MAX,
    ensures
        ((a)@) == ((old(a))@) + ((b)@),
        ((b)@) == ((b)@),
{
    *a += *b;
    *a
}

fn CheckPre_incr_a_by_b(old_a: &i32, b: &i32)
    requires
        i32::MIN <= ((old_a)@) + ((b)@) <= i32::MAX,
{}

fn CheckPost_incr_a_by_b(old_a: &i32, a: &i32, b: &i32, result: i32)
    requires
        ((a)@) == ((old_a)@) + ((b)@),
        ((b)@) == ((b)@),
{}

fn main() {
}

fn valid_test_harness_incr_a_by_b() {
    // Test case 1: Valid - positive integers
    let a1 = 5;
    let b1 = 3;
    CheckPre_incr_a_by_b(&a1, &b1);
    let new_a1 = 8;
    let result1 = 8;
    CheckPost_incr_a_by_b(&a1, &new_a1, &b1, result1);

    // Test case 2: Valid - negative integers
    let a2 = -2;
    let b2 = -3;
    CheckPre_incr_a_by_b(&a2, &b2);
    let new_a2 = -5;
    let result2 = -5;
    CheckPost_incr_a_by_b(&a2, &new_a2, &b2, result2);

    // Test case 3: Valid - mixed sign integers
    let a3 = 10;
    let b3 = -5;
    CheckPre_incr_a_by_b(&a3, &b3);
    let new_a3 = 5;
    let result3 = 5;
    CheckPost_incr_a_by_b(&a3, &new_a3, &b3, result3);

    // Test case 4: Valid - zero and positive integer
    let a4 = 0;
    let b4 = 42;
    CheckPre_incr_a_by_b(&a4, &b4);
    let new_a4 = 42;
    let result4 = 42;
    CheckPost_incr_a_by_b(&a4, &new_a4, &b4, result4);

    // Test case 5: Valid - zero sum
    let a5 = -100;
    let b5 = 100;
    CheckPre_incr_a_by_b(&a5, &b5);
    let new_a5 = 0;
    let result5 = 0;
    CheckPost_incr_a_by_b(&a5, &new_a5, &b5, result5);

    // Test case 6: Boundary - sum equals i32::MAX
    let a6 = i32::MAX;
    let b6 = 0;
    CheckPre_incr_a_by_b(&a6, &b6);
    let new_a6 = i32::MAX;
    let result6 = i32::MAX;
    CheckPost_incr_a_by_b(&a6, &new_a6, &b6, result6);

    // Test case 7: Boundary - sum equals i32::MIN
    let a7 = i32::MIN;
    let b7 = 0;
    CheckPre_incr_a_by_b(&a7, &b7);
    let new_a7 = i32::MIN;
    let result7 = i32::MIN;
    CheckPost_incr_a_by_b(&a7, &new_a7, &b7, result7);
}

fn invalid_test_harness_incr_a_by_b() {
    // Test case 8: Invalid - NULL pointer simulation
    // CheckPre_incr_a_by_b(None, &5);
}

} // verus!

// RAC
// fn incr_a_by_b(a: &mut i32, b: &i32) -> i32
// {
//     *a += *b;
//     *a
// }


// fn main() {
//     invalid_test_harness_incr_a_by_b();
// }

// fn invalid_test_harness_incr_a_by_b() {
//     // Test case 9: Invalid - Overlapping pointers simulation
//     // Note: Rust's borrow checker prevents this at compile time if using &mut.
//     // We simulate the address check in the helper.
//     let a9 = 5;
//     incr_a_by_b(&a9, &a9);
// }