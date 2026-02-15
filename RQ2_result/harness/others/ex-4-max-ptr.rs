static mut h: i32 = 0;

fn CheckPost_max_ptr(old_a: &i32, old_b: &i32, a: &i32, b: &i32)
{
    assert!(
        (!((*(old_a)) < (*(old_b))) || ((*(a)) == (*(old_b)) && (*(b)) == (*(old_a)))) &&
        (!((*(old_a)) >= (*(old_b))) || ((*(a)) == (*(old_a)) && (*(b)) == (*(old_b))))
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
    assert!(a == 42 && b == 24);
    unsafe { assert!(h == 42); }
}

fn valid_test_harness_max_ptr() {
    // --- Test Case 1: Valid - a < b ---
    let (mut a1, mut b1) = (24, 42);
    let (old_a1, old_b1) = (a1, b1);
    max_ptr(&mut a1, &mut b1);
    // Simulation of function logic: swap occurs
    let (res_a1, res_b1) = (42, 24); 
    CheckPost_max_ptr(&old_a1, &old_b1, &res_a1, &res_b1);

    // --- Test Case 2: Valid - a > b ---
    let (mut a2, mut b2) = (50, 30);
    let (old_a2, old_b2) = (a2, b2);
    max_ptr(&mut a2, &mut b2);
    // Simulation: no swap
    let (res_a2, res_b2) = (50, 30);
    CheckPost_max_ptr(&old_a2, &old_b2, &res_a2, &res_b2);

    // --- Test Case 3: Valid - a == b ---
    let (mut a3, mut b3) = (10, 10);
    let (old_a3, old_b3) = (a3, b3);
    max_ptr(&mut a3, &mut b3);
    let (res_a3, res_b3) = (10, 10);
    CheckPost_max_ptr(&old_a3, &old_b3, &res_a3, &res_b3);

    // --- Test Case 4: Valid - a negative, b positive ---
    let (mut a4, mut b4) = (-5, 3);
    let (old_a4, old_b4) = (a4, b4);
    max_ptr(&mut a4, &mut b4);
    let (res_a4, res_b4) = (3, -5);
    CheckPost_max_ptr(&old_a4, &old_b4, &res_a4, &res_b4);

    // --- Test Case 5: Valid - a larger positive ---
    let (mut a5, mut b5) = (100, 50);
    let (old_a5, old_b5) = (a5, b5);
    max_ptr(&mut a5, &mut b5);
    let (res_a5, res_b5) = (100, 50);
    CheckPost_max_ptr(&old_a5, &old_b5, &res_a5, &res_b5);

    // --- Test Case 8: Boundary - Negative and Zero ---
    let (mut a8, mut b8) = (-1, 0);
    let (old_a8, old_b8) = (a8, b8);
    max_ptr(&mut a8, &mut b8);
    // Zero is greater than -1
    let (res_a8, res_b8) = (0, -1);
    CheckPost_max_ptr(&old_a8, &old_b8, &res_a8, &res_b8);

    // --- Test Case 9: Boundary - INT_MIN and INT_MAX ---
    let (mut a9, mut b9) = (i32::MIN, i32::MAX);
    let (old_a9, old_b9) = (a9, b9);
    max_ptr(&mut a9, &mut b9);
    let (res_a9, res_b9) = (i32::MAX, i32::MIN);
    CheckPost_max_ptr(&old_a9, &old_b9, &res_a9, &res_b9);
}

fn invalid_test_harness_max_ptr() {
    // --- Test Case 6: Invalid - a is NULL ---
    // Violates: requires \valid(a)
    unsafe {
        let mut b6 = 42;
        let null_ptr: *mut i32 = std::ptr::null_mut();
        max_ptr(&mut *null_ptr, &mut b6);
    }

    // --- Test Case 7: Invalid - b is NULL ---
    // Violates: requires \valid(b)
    unsafe {
        let mut a7 = 24;
        let null_ptr: *mut i32 = std::ptr::null_mut();
        max_ptr(&mut a7, &mut *null_ptr);
    }
}