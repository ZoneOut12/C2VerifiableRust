fn CheckPre_search(old_array: &[i32], length: usize, element: i32)
{
    assert!(
        old_array.len() >= length
    );
}

unsafe fn CheckPost_search(old_array: &[i32], array: &[i32], length: usize, element: i32, result: Option<&i32>)
{
    assert!(       
        (!(0..length).all(|off| !(old_array[(off) as usize] != element)) || result.is_none()) &&
        ((0..length).all(|off| !(old_array[(off) as usize] == element)) || (((array.as_ptr()
            <= (result.unwrap() as *const i32) && (result.unwrap() as *const i32) < array.as_ptr().add(length)) && (*(result).unwrap() == element))))
    );
}

fn search(array: &mut [i32], length: usize, element: i32) -> Option<&mut i32>
{
    let mut i: usize = 0;
    while i < length
    {
        let old_measure = length - i;
        assert!(
            0 <= i && i <= length &&
            (0..i).all(|j| array[(j) as usize] != element)
        );
        if array[i] == element {
            return Some(&mut array[i]);
        }
        i += 1;
        assert!(old_measure > length - i);
    }
    assert!(
        0 <= i && i <= length &&
        (0..i).all(|j| array[(j) as usize] != element)
    );
    None
}

fn main() {
    unsafe{
        valid_test_harness_search();
    }
    // invalid_test_harness_search();
}

unsafe fn valid_test_harness_search() {
    // Shared parameters
    let mut ov_buf = [0i32; 10]; 

    // --- Test Case 1: Valid - element in middle ---
    let mut arr1 = [1, 2, 3, 4];
    CheckPre_search(&arr1, 4, 3);
    // Logic: find 3 at index 2
    let res1 = Some(&arr1[2]);
    CheckPost_search(&[1, 2, 3, 4], &arr1, 4, 3, res1);
    search(&mut arr1, 4, 3);

    // --- Test Case 2: Valid - element at start ---
    let mut arr2 = [5, 6, 7];
    CheckPre_search(&arr2, 3, 5);
    // Logic: find 5 at index 0
    let res2 = Some(&arr2[0]);
    CheckPost_search(&[5, 6, 7], &arr2, 3, 5, res2);
    search(&mut arr2, 3, 5);

    // --- Test Case 3: Valid - element at end ---
    let mut arr3 = [10, 20];
    CheckPre_search(&arr3, 2, 20);
    // Logic: find 20 at index 1
    let res3 = Some(&arr3[1]);
    CheckPost_search(&[10, 20], &arr3, 2, 20, res3);
    search(&mut arr3, 2, 20);

    // --- Test Case 4: Valid - single element not found ---
    let mut arr4 = [42];
    CheckPre_search(&arr4, 1, 99);
    // Logic: not found
    let res4: Option<&i32> = None;
    CheckPost_search(&[42], &arr4, 1, 99, res4);
    search(&mut arr4, 1, 99);

    // --- Test Case 5: Valid - multiple elements not found ---
    let mut arr5 = [1, 3, 5];
    CheckPre_search(&arr5, 3, 2);
    let res5: Option<&i32> = None;
    CheckPost_search(&[1, 3, 5], &arr5, 3, 2, res5);
    search(&mut arr5, 3, 2);

    // --- Test Case 6: Boundary - empty array ---
    let mut arr6: [i32; 0] = [];
    CheckPre_search(&arr6, 0, 5);
    let res6: Option<&i32> = None;
    CheckPost_search(&[], &arr6, 0, 5, res6);
    search(&mut arr6, 0, 5);

    // --- Test Case 7: Boundary - element at last position ---
    let mut arr7 = [7, 8, 9];
    CheckPre_search(&arr7, 3, 9);
    let res7 = Some(&arr7[2]);
    CheckPost_search(&[7, 8, 9], &arr7, 3, 9, res7);
    search(&mut arr7, 3, 9);
}

fn invalid_test_harness_search() {
    // --- Test Case 8: Invalid - NULL array pointer ---
    // CheckPre_search(None, 5, 3);

    // --- Test Case 9: Invalid - length exceeds array size ---
    // Violates: \valid_read(array + (0..length-1))
    let arr9_real = [1, 2];
    CheckPre_search(&arr9_real, 3, 0);
}