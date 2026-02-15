static mut h: i32 = 0;

fn CheckPost_max_ptr(a: &i32, b: &i32, result: i32)
{
    assert!(
        (!((*(a))<(*(b))) || (result==(*(b)))) &&
        (!((*(a))>=(*(b))) || (result==(*(a)))) &&
        result==(*(a))||result==(*(b)),
    );
}

fn max_ptr(a: &i32, b: &i32) -> i32
{
    if *a < *b { *b } else { *a }
}


fn main() {
    valid_test_harness_max_ptr();

    unsafe { h = 42; }
    let a: i32 = 24;
    let b: i32 = 42;
    let x: i32 = max_ptr(&a, &b);
    assert!(x==42);
    unsafe { assert!(h==42); }
}

fn valid_test_harness_max_ptr() {
    // --- Test Case 1: Valid - original case ---
    let (a1, b1) = (24, 42);
    max_ptr(&a1, &b1);
    let result1 = 42;
    CheckPost_max_ptr(&a1, &b1, result1);

    // --- Test Case 2: Valid - a > b ---
    let (a2, b2) = (50, 30);
    max_ptr(&a2, &b2);
    let result2 = 50;
    CheckPost_max_ptr(&a2, &b2, result2);

    // --- Test Case 3: Valid - a negative, b positive ---
    let (a3, b3) = (-5, 3);
    max_ptr(&a3, &b3);
    let result3 = 3;
    CheckPost_max_ptr(&a3, &b3, result3);

    // --- Test Case 4: Valid - both zero ---
    let (a4, b4) = (0, 0);
    max_ptr(&a4, &b4);
    let result4 = 0;
    CheckPost_max_ptr(&a4, &b4, result4);

    // --- Test Case 5: Valid - extreme values ---
    let (a5, b5) = (i32::MAX, i32::MIN);
    max_ptr(&a5, &b5);
    let result5 = i32::MAX;
    CheckPost_max_ptr(&a5, &b5, result5);

    // --- Test Case 6: Boundary - equal values ---
    let (a6, b6) = (42, 42);
    max_ptr(&a6, &b6);
    let result6 = 42;
    CheckPost_max_ptr(&a6, &b6, result6);

    // --- Test Case 7: Boundary - same pointer (aliasing) ---
    let val7 = 42;
    // Note: Rust references allow multiple immutable borrows to the same value
    max_ptr(&val7, &val7);
    let result7 = 42;
    CheckPost_max_ptr(&val7, &val7, result7);
}

fn invalid_test_harness_max_ptr() {
    // // --- Test Case 8: Invalid - a is NULL ---
    // let b8 = 42;
    // max_ptr(None, &b8);

    // // --- Test Case 9: Invalid - b is NULL ---
    // let a9 = 24;
    // max_ptr(&a9, None);
}