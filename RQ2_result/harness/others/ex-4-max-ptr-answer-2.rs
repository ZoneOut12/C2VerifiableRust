static mut h: i32 = 0;

fn CheckPost_max_ptr(old_a: &i32, old_b: &i32, a: &i32, b: &i32)
{
    assert!(
        (!((*(old_a)) < (*(old_b))) || ((*(a)) == (*(old_b)) && (*(b)) == (*(old_a)))),
        (!((*(old_a)) >= (*(old_b))) || ((*(a)) == (*(old_a)) && (*(b)) == (*(old_b)))),
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
    // --- Test Case 1: Standard Swap (a < b) ---
    let (mut a1, mut b1) = (24, 42);
    let old_a1 = a1;
    let old_b1 = b1;
    max_ptr(&mut a1, &mut b1);
    // Logic: a becomes 42, b becomes 24
    let (res_a1, res_b1) = (42, 24);
    CheckPost_max_ptr(&old_a1, &old_b1, &res_a1, &res_b1);

    // --- Test Case 2: No Swap Needed (a > b) ---
    let (mut a2, mut b2) = (50, 30);
    let old_a2 = a2;
    let old_b2 = b2;
    max_ptr(&mut a2, &mut b2);
    let (res_a2, res_b2) = (50, 30);
    CheckPost_max_ptr(&old_a2, &old_b2, &res_a2, &res_b2);

    // --- Test Case 3: Negative Values (a < b) ---
    let (mut a3, mut b3) = (-10, -5);
    let old_a3 = a3;
    let old_b3 = b3;
    max_ptr(&mut a3, &mut b3);
    let (res_a3, res_b3) = (-5, -10);
    CheckPost_max_ptr(&old_a3, &old_b3, &res_a3, &res_b3);

    // --- Test Case 4: Zero and Negative (a > b) ---
    let (mut a4, mut b4) = (0, -100);
    let old_a4 = a4;
    let old_b4 = b4;
    max_ptr(&mut a4, &mut b4);
    let (res_a4, res_b4) = (0, -100);
    CheckPost_max_ptr(&old_a4, &old_b4, &res_a4, &res_b4);

    // --- Test Case 5: Extreme Values (INT_MIN/MAX) ---
    let (mut a5, mut b5) = (i32::MIN, i32::MAX);
    let old_a5 = a5;
    let old_b5 = b5;
    max_ptr(&mut a5, &mut b5);
    let (res_a5, res_b5) = (i32::MAX, i32::MIN);
    CheckPost_max_ptr(&old_a5, &old_b5, &res_a5, &res_b5);

    // --- Test Case 6: Boundary - Equal Values ---
    let (mut a6, mut b6) = (42, 42);
    let old_a6 = a6;
    let old_b6 = b6;
    max_ptr(&mut a6, &mut b6);
    let (res_a6, res_b6) = (42, 42);
    CheckPost_max_ptr(&old_a6, &old_b6, &res_a6, &res_b6);

    // --- Test Case 7: Boundary - Large Negative Values (a < b) ---
    // Testing logic with values far from zero
    let (mut a7, mut b7) = (-100000, -500);
    let (old_a7, old_b7) = (a7, b7);
    max_ptr(&mut a7, &mut b7);
    // -500 is greater than -100000
    let (res_a7, res_b7) = (-500, -100000);
    CheckPost_max_ptr(&old_a7, &old_b7, &res_a7, &res_b7);
}

fn invalid_test_harness_max_ptr() {
    // // --- Test Case 8: Invalid - NULL pointer for 'a' ---
    // let b8 = 42;
    // max_ptr(None, &b8);

    // // --- Test Case 9: Invalid - NULL pointer for 'b' ---
    // let a9 = 24;
    // max_ptr(&a9, None);
}