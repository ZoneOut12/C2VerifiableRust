static mut h: i32 = 0;

fn CheckPost_max_ptr(a: &i32, b: &i32, result: i32)
{
    assert!(
        result == (*(a)) || result == (*(b)) &&
        (!((*(a)) < (*(b))) || (result == (*(b)))) &&
        (!((*(a)) > (*(b))) || (result == (*(a)))) &&
        (!((*(a)) == (*(b))) || (result == (*(a)) && (*(a)) == (*(b))))
    );
}

fn max_ptr(a: &i32, b: &i32) -> i32
{
    if *a < *b {
        *b
    } else {
        *a
    }
}

fn main() {
    valid_test_harness_max_ptr();

    unsafe {
        h = 42;
    }
    let a: i32 = 24;
    let b: i32 = 42;
    let x: i32 = max_ptr(&a, &b);
    assert!(x == 42);
    unsafe { assert!(h == 42); }
}

fn valid_test_harness_max_ptr() {
    // --- Test Case 1: Valid - a < b ---
    let (a1, b1) = (10, 20);
    max_ptr(&a1, &b1);
    let result1 = 20;
    CheckPost_max_ptr(&a1, &b1, result1);

    // --- Test Case 2: Valid - a > b ---
    let (a2, b2) = (30, 15);
    max_ptr(&a2, &b2);
    let result2 = 30;
    CheckPost_max_ptr(&a2, &b2, result2);

    // --- Test Case 3: Valid - a == b ---
    let (a3, b3) = (5, 5);
    max_ptr(&a3, &b3);
    let result3 = 5;
    CheckPost_max_ptr(&a3, &b3, result3);

    // --- Test Case 4: Valid - negative and positive ---
    let (a4, b4) = (-5, 5);
    max_ptr(&a4, &b4);
    let result4 = 5;
    CheckPost_max_ptr(&a4, &b4, result4);

    // --- Test Case 5: Valid - both zero ---
    let (a5, b5) = (0, 0);
    max_ptr(&a5, &b5);
    let result5 = 0;
    CheckPost_max_ptr(&a5, &b5, result5);

    // --- Test Case 8: Boundary - i32::MIN and i32::MAX ---
    let (a8, b8) = (i32::MIN, i32::MAX);
    max_ptr(&a8, &b8);
    let result8 = i32::MAX;
    CheckPost_max_ptr(&a8, &b8, result8);

    // --- Test Case 9: Boundary - same pointer (aliasing) ---
    let val9 = 5;
    // Rust allows multiple immutable references to the same data
    max_ptr(&val9, &val9);
    let result9 = 5;
    CheckPost_max_ptr(&val9, &val9, result9);
}

fn invalid_test_harness_max_ptr() {
    // // --- Test Case 6: Invalid - a is NULL ---
    // let b6 = 42;
    // max_ptr(None, &b6);

    // // --- Test Case 7: Invalid - b is NULL ---
    // let a7 = 24;
    // max_ptr(&a7, None);
}