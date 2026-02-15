static mut h: i32 = 0;

fn CheckPost_max_ptr(a: Option<&i32>, b: Option<&i32>, result: i32)
{
    assert!(
        (result == i32::MIN || (a.is_some() && result == (*(a).unwrap())) || (b.is_some() && result == (*(b).unwrap()))) &&
        (!((a).is_none() && (b).is_none()) || (result == i32::MIN)) && 
        (!((a).is_none() && (b).is_some()) || (result == (*(b).unwrap()))) &&
        (!((a).is_some() && (b).is_none()) || (result == (*(a).unwrap()))) &&
        (!((a).is_some() && (b).is_some() && (*(a).unwrap()) >= (*(b).unwrap())) || (result == (*(
        a).unwrap()))) &&
        (!((a).is_some() && (b).is_some() && (*(a).unwrap()) < (*(b).unwrap())) || (result == (*(
        b).unwrap())))
    );
}


fn max_ptr(a: Option<&i32>, b: Option<&i32>) -> i32
{
    if a.is_none() && b.is_none() {
        return i32::MIN;
    }
    if a.is_none() {
        return *b.unwrap();
    }
    if b.is_none() {
        return *a.unwrap();
    }
    let a_val = a.unwrap();
    let b_val = b.unwrap();
    if *a_val < *b_val {
        *b_val
    } else {
        *a_val
    }
}

fn main() {
    valid_test_harness_max_ptr();
    // invalid_test_harness_max_ptr();

    unsafe {
        h = 42;
    }
    let a: i32 = 24;
    let b: i32 = 42;
    let x: i32 = max_ptr(Some(&a), Some(&b));
    assert!(x == 42);
    unsafe { assert!(h == 42); }
}

fn valid_test_harness_max_ptr() {
    // --- Test Case 1: Valid - both NULL (Option::None) ---
    let (a1, b1) = (None, None);
    max_ptr(a1, b1);
    let result1 = i32::MIN;
    CheckPost_max_ptr(a1, b1, result1);

    // --- Test Case 2: Valid - a NULL, b valid ---
    let b_val2 = 30;
    let (a2, b2) = (None, Some(&b_val2));
    max_ptr(a2, b2);
    let result2 = 30;
    CheckPost_max_ptr(a2, b2, result2);

    // --- Test Case 3: Valid - b NULL, a valid ---
    let a_val3 = 25;
    let (a3, b3) = (Some(&a_val3), None);
    max_ptr(a3, b3);
    let result3 = 25;
    CheckPost_max_ptr(a3, b3, result3);

    // --- Test Case 4: Valid - both valid, a >= b ---
    let (a_val4, b_val4) = (50, 30);
    let (a4, b4) = (Some(&a_val4), Some(&b_val4));
    max_ptr(a4, b4);
    let result4 = 50;
    CheckPost_max_ptr(a4, b4, result4);

    // --- Test Case 5: Valid - both valid, a < b ---
    let (a_val5, b_val5) = (30, 50);
    let (a5, b5) = (Some(&a_val5), Some(&b_val5));
    max_ptr(a5, b5);
    let result5 = 50;
    CheckPost_max_ptr(a5, b5, result5);

    // --- Test Case 6: Boundary - both valid and equal ---
    let (a_val6, b_val6) = (50, 50);
    let (a6, b6) = (Some(&a_val6), Some(&b_val6));
    max_ptr(a6, b6);
    let result6 = 50;
    CheckPost_max_ptr(a6, b6, result6);

    // --- Test Case 7: Boundary - extreme values ---
    let (a_val7, b_val7) = (i32::MIN, i32::MAX);
    let (a7, b7) = (Some(&a_val7), Some(&b_val7));
    max_ptr(a7, b7);
    let result7 = i32::MAX;
    CheckPost_max_ptr(a7, b7, result7);
}

fn invalid_test_harness_max_ptr() {
    // --- Test Case 8: Invalid - a is invalid pointer (0x1) ---
    unsafe {
        let b_val8 = 100;
        let invalid_a: *const i32 = 0x1 as *const i32;
        max_ptr(Some(&*invalid_a), Some(&b_val8));
    }

    // --- Test Case 9: Invalid - b is invalid pointer (0x1) ---
    unsafe {
        let a_val9 = 100;
        let invalid_b: *const i32 = 0x1 as *const i32;
        max_ptr(Some(&a_val9), Some(&*invalid_b));
    }
}