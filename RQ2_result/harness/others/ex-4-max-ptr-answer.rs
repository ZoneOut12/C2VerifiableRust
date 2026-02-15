static mut h: i32 = 0;

fn CheckPost_max_ptr(old_a: &i32, old_b: &i32, a: &i32, b: &i32)
{
    assert!(
        (!(*(old_a) < *(old_b)) || (*(a) == *(old_b) && *(b) == *(old_a))) &&
	    (!(*(old_a) >= *(old_b)) || (*(a) == *(old_a) && *(b) == *(old_b)))
    );
}

fn max_ptr(a: &mut i32, b: &mut i32)
{
    if *a < *b {
        let tmp: i32 = *b;
        *b = *a;
        *a = tmp;
    }
}

fn main() {
    valid_test_harness_max_ptr();
    // invalid_test_harness_max_ptr();

    unsafe {
        h = 42;
    }
    let mut a: i32 = 24;
    let mut b: i32 = 42;
    max_ptr(&mut a, &mut b);
    assert!(a==42&&b==24);
    unsafe { assert!(h==42); }
}

fn valid_test_harness_max_ptr() {
    // --- Test Case 1: Trigger behavior 'reorder' (a < b) ---
    let (mut a1, mut b1) = (10, 20);
    let (old_a1, old_b1) = (a1, b1);
    // Logic: a becomes 20, b becomes 10
    let (res_a1, res_b1) = (20, 10);
    CheckPost_max_ptr(&old_a1, &old_b1, &res_a1, &res_b1);
    max_ptr(&mut a1, &mut b1);

    // --- Test Case 2: Trigger behavior 'do_not_change' (a > b) ---
    let (mut a2, mut b2) = (30, 15);
    let (old_a2, old_b2) = (a2, b2);
    // Logic: no change
    let (res_a2, res_b2) = (30, 15);
    CheckPost_max_ptr(&old_a2, &old_b2, &res_a2, &res_b2);
    max_ptr(&mut a2, &mut b2);

    // --- Test Case 3: Trigger behavior 'do_not_change' (a == b) ---
    let (mut a3, mut b3) = (42, 42);
    let (old_a3, old_b3) = (a3, b3);
    let (res_a3, res_b3) = (42, 42);
    CheckPost_max_ptr(&old_a3, &old_b3, &res_a3, &res_b3);
    max_ptr(&mut a3, &mut b3);

    // --- Test Case 4: Reorder with negative values (a < b) ---
    let (mut a4, mut b4) = (-50, -10);
    let (old_a4, old_b4) = (a4, b4);
    let (res_a4, res_b4) = (-10, -50);
    CheckPost_max_ptr(&old_a4, &old_b4, &res_a4, &res_b4);
    max_ptr(&mut a4, &mut b4);

    // --- Test Case 5: Reorder with zero and negative ---
    let (mut a5, mut b5) = (-1, 0);
    let (old_a5, old_b5) = (a5, b5);
    let (res_a5, res_b5) = (0, -1);
    CheckPost_max_ptr(&old_a5, &old_b5, &res_a5, &res_b5);
    max_ptr(&mut a5, &mut b5);

    // --- Test Case 6: Boundary - Extreme values (i32::MIN/MAX) ---
    let (mut a6, mut b6) = (i32::MIN, i32::MAX);
    let (old_a6, old_b6) = (a6, b6);
    let (res_a6, res_b6) = (i32::MAX, i32::MIN);
    CheckPost_max_ptr(&old_a6, &old_b6, &res_a6, &res_b6);
    max_ptr(&mut a6, &mut b6);

    // --- Test Case 7: Verification of 'do_not_change' with high values ---
    let (mut a7, mut b7) = (100, 99);
    let (old_a7, old_b7) = (a7, b7);
    let (res_a7, res_b7) = (100, 99);
    CheckPost_max_ptr(&old_a7, &old_b7, &res_a7, &res_b7);
    max_ptr(&mut a7, &mut b7);
}

fn invalid_test_harness_max_ptr() {
    // --- Test Case 8: Invalid - NULL pointer for 'a' ---
    // Violates: requires \valid(a)
    unsafe {
        let mut b8 = 42;
        let null_a: *mut i32 = std::ptr::null_mut();
        // Simulating the passing of a null/invalid pointer to the checker
        max_ptr(&mut *null_a, &mut b8);
    }

    // --- Test Case 9: Invalid - b is an invalid memory address ---
    // Violates: requires \valid(b)
    unsafe {
        let mut a9 = 24;
        let invalid_b: *mut i32 = 0x123 as *mut i32;
        max_ptr(&mut a9, &mut *invalid_b);
    }
}