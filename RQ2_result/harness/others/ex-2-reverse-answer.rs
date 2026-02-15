fn swap(a: &mut i32, b: &mut i32)
{
    let tmp: i32 = *a;
    *a = *b;
    *b = tmp;
}

fn CheckPre_reverse(old_array: &[i32], len: usize)
{
    assert!(
        old_array.len() >= len
    );
}

fn reverse(array: &mut [i32], len: usize)
{
    let mut i: usize = 0;
    while i < len / 2
    {
        let old_measure = len - i;
        assert!(0 <= i && i <= len / 2);
        let right_i = len - i - 1;
        let (left, right) = array.split_at_mut(right_i);
        swap(&mut left[i], &mut right[0]);
        i += 1;
        assert!(old_measure > len - i);
    }
    assert!(0 <= i && i <= len / 2);
}

fn main() {
    valid_test_harness_swap();
    invalid_test_harness_swap();
    valid_test_harness_reverse();
    invalid_test_harness_reverse();
}

fn valid_test_harness_swap() {
    // --- Test Case 1: Standard swap ---
    let (mut a1, mut b1) = (10, 20);
    swap(&mut a1, &mut b1);

    // --- Test Case 2: Swapping identical values ---
    let (mut a2, mut b2) = (42, 42);
    swap(&mut a2, &mut b2);

    // --- Test Case 3: Swapping with zero ---
    let (mut a3, mut b3) = (0, 100);
    swap(&mut a3, &mut b3);

    // --- Test Case 4: Swapping negative numbers ---
    let (mut a4, mut b4) = (-1, -50);
    swap(&mut a4, &mut b4);

    // --- Test Case 5: Big values ---
    let (mut a5, mut b5) = (100, 300);
    swap(&mut a5, &mut b5);

    // --- Test Case 6: Boundary - INT_MAX and INT_MIN ---
    let (mut a6, mut b6) = (i32::MAX, i32::MIN);
    swap(&mut a6, &mut b6);

    // --- Test Case 7: Heap-allocated values ---
    let mut a7 = Box::new(5);
    let mut b7 = Box::new(10);
    swap(&mut *a7, &mut *b7);
}

fn valid_test_harness_reverse() {
    // --- Test Case 1: Valid even-length array ---
    let mut arr1 = [1, 2, 3, 4];
    CheckPre_reverse(&arr1, 4);
    reverse(&mut arr1, 4);

    // --- Test Case 2: Valid odd-length array ---
    let mut arr2 = [5, 6, 7];
    CheckPre_reverse(&arr2, 3);
    reverse(&mut arr2, 3);

    // --- Test Case 3: Valid array with negative numbers ---
    let mut arr3 = [-1, -2, -3];
    CheckPre_reverse(&arr3, 3);
    reverse(&mut arr3, 3);

    // --- Test Case 4: Valid array of zeros ---
    let mut arr4 = [0, 0, 0];
    CheckPre_reverse(&arr4, 3);
    reverse(&mut arr4, 3);

    // --- Test Case 5: Valid array with mixed values ---
    let mut arr5 = [1, -2, 3, -4];
    CheckPre_reverse(&arr5, 4);
    reverse(&mut arr5, 4);

    // --- Test Case 6: Boundary empty array (len=0) ---
    let mut arr6 = [0; 0]; 
    CheckPre_reverse(&arr6, 0);
    reverse(&mut arr6, 0);

    // --- Test Case 7: Boundary single-element array (len=1) ---
    let mut arr7 = [42];
    CheckPre_reverse(&arr7, 1);
    reverse(&mut arr7, 1);
}

fn invalid_test_harness_reverse() {
    // // --- Test Case 8: Invalid null array pointer ---
    // // Note: To pass a "null" to a slice, we must bypass safe Rust
    // unsafe {
    //     let null_slice: &[i32] = std::slice::from_raw_parts(std::ptr::null(), 0);
    //     CheckPre_reverse(null_slice, 2);
    // }

    // // --- Test Case 9: Invalid array length (buffer overflow) ---
    // // Passing a length that exceeds the actual slice length
    // let arr9 = [5];
    // CheckPre_reverse(&arr9, 2); 
}

fn invalid_test_harness_swap() {
    // // --- Test Case 8: Invalid - NULL pointer for a ---
    // // Violates \valid(a)
    // let ptr_a: *mut i32 = std::ptr::null_mut();
    // let mut b8 = 10;
    // unsafe { swap(ptr_a, &mut b8) };

    // // --- Test Case 9: Invalid - Dangling pointer or unmapped memory ---
    // // Violates \valid(b)
    // let mut a9 = 5;
    // let ptr_b: *mut i32 = 0x12345 as *mut i32; // Arbitrary invalid address
    // unsafe { swap(&mut a9, ptr_b) };
}
