fn zeroed(a: &[i32], b: usize, e: usize) -> bool {
    if b >= e {
        return true;
    }
    a[e - 1] == 0 && zeroed(a, b, e - 1)
}

fn CheckPre_reset(old_array: &[i32], length: usize)
{
    assert!(old_array.len() >= length);
}

fn CheckPost_reset(array: &[i32], length: usize)
{
    assert!(
        zeroed(array, 0 , length)
    );
}

fn reset(array: &mut [i32], length: usize)
{
    let mut i: usize = 0;
    while i < length
    {
        let old_measure = length - i;
        assert!(
            0 <= i && i <= length &&
            zeroed(array, 0, i)
        );
        array[i] = 0;
        i += 1;
        assert!(old_measure > length - i);
    }
    assert!(
        0 <= i && i <= length &&
        zeroed(array, 0, i)
    );
}

fn main() {
    valid_test_harness_reset();
    // invalid_test_harness_reset();
}

fn valid_test_harness_reset() {
    // --- Test Case 1: Valid - normal array ---
    let mut arr1 = [1, 2, 3, 4, 5];
    CheckPre_reset(&arr1, 5);
    // Logic: reset all to 0
    let res1 = [0, 0, 0, 0, 0];
    CheckPost_reset(&res1, 5);
    reset(&mut arr1, 5);

    // --- Test Case 2: Valid - single element ---
    let mut arr2 = [7];
    CheckPre_reset(&arr2, 1);
    let res2 = [0];
    CheckPost_reset(&res2, 1);
    reset(&mut arr2, 1);

    // --- Test Case 3: Valid - longer array ---
    let mut arr3 = [5i32; 10];
    CheckPre_reset(&arr3, 10);
    let res3 = [0i32; 10];
    CheckPost_reset(&res3, 10);
    reset(&mut arr3, 10);

    // --- Test Case 4: Valid - already zeros ---
    let mut arr4 = [0, 0, 0];
    CheckPre_reset(&arr4, 3);
    let res4 = [0, 0, 0];
    CheckPost_reset(&res4, 3);
    reset(&mut arr4, 3);

    // --- Test Case 5: Valid - mixed values ---
    let mut arr5 = [1, -1, 2];
    CheckPre_reset(&arr5, 3);
    let res5 = [0, 0, 0];
    CheckPost_reset(&res5, 3);
    reset(&mut arr5, 3);

    // --- Test Case 6: Boundary - zero-length array ---
    // In C, \valid(array + (0..-1)) is vacuously true.
    let mut arr6: [i32; 0] = [];
    CheckPre_reset(&arr6, 0);
    CheckPost_reset(&arr6, 0);
    reset(&mut arr6, 0);

    // --- Test Case 7: Boundary - smallest non-zero length ---
    let mut arr7 = [42];
    CheckPre_reset(&arr7, 1);
    let res7 = [0];
    CheckPost_reset(&res7, 1);
    reset(&mut arr7, 1);
}

fn invalid_test_harness_reset() {
    // --- Test Case 8: Invalid - NULL pointer with non-zero length ---
    // CheckPre_reset(None, 3);

    // --- Test Case 9: Invalid - array too small ---
    // Violates: \valid(array + (0 .. 2)) when only 2 elements exist
    let mut arr9 = [1, 2];
    CheckPre_reset(&arr9, 3);
}