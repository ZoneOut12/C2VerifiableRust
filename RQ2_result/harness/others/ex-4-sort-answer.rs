fn CheckPre_min_idx_in(a: &[i32], beg: usize, end: usize)
{
    assert!(
        beg < end &&
        a.len() >= end
    );
}

fn CheckPost_min_idx_in(a: &[i32], beg: usize, end: usize, result: usize)
{
    assert!(
        beg <= result && result < end
    );
}

fn min_idx_in(a: &[i32], beg: usize, end: usize) -> usize
{
    let mut min_i: usize = beg;
    let mut i: usize = beg + 1;
    while i < end
    {
        let old_measure = end - i;
        assert!(
            beg + 1 <= i && i <= end &&
            beg <= min_i && min_i < end
        );
        if a[i] < a[min_i] {
            min_i = i;
        }
        i += 1;
        assert!(old_measure > end - i);
    }
    assert!(
        beg + 1 <= i && i <= end &&
        beg <= min_i && min_i < end
    );
    min_i
}

fn CheckPre_swap(p: &mut i32, q: &mut i32)
{}

fn swap(p: &mut i32, q: &mut i32)
{
    let tmp: i32 = *p;
    *p = *q;
    *q = tmp;
}

fn CheckPre_sort(old_a: &[i32], beg: usize, end: usize)
{
    assert!(
        beg <= end &&
        old_a.len() >= end
    );
}

fn sort(a: &mut [i32], beg: usize, end: usize)
{
    let mut i: usize = beg;
    while i < end
    {
        let old_measure = end - i;
        assert!(beg <= i && i <= end);
        let imin: usize = min_idx_in(a, i, end);
        if i != imin {
            let (left, right) = a.split_at_mut(imin);
            swap(&mut left[i], &mut right[0]);
        }
        i += 1;
        assert!(old_measure > end - i);
    }
    assert!(beg <= i && i <= end);
}

fn main() {
    valid_test_harness_min_idx_in();
    valid_test_harness_swap();
    valid_test_harness_sort();
    // invalid_test_harness_sort();
    // invalid_test_harness_swap();
    // invalid_test_harness_min_idx_in();
}

fn valid_test_harness_sort() {
    // --- Test Case 1: Normal array ---
    let mut a1 = [5, 3, 2, 4];
    CheckPre_sort(&a1, 0, 4);
    // After sort: [2, 3, 4, 5]
    sort(&mut a1, 0, 4);

    // --- Test Case 2: Single element ---
    let mut a2 = [42];
    CheckPre_sort(&a2, 0, 1);
    sort(&mut a2, 0, 1);

    // --- Test Case 3: Already sorted ---
    let mut a3 = [1, 2, 3, 4];
    CheckPre_sort(&a3, 0, 4);
    sort(&mut a3, 0, 4);

    // --- Test Case 4: Descending order ---
    let mut a4 = [4, 3, 2, 1];
    CheckPre_sort(&a4, 0, 4);
    sort(&mut a4, 0, 4);

    // --- Test Case 5: Duplicates ---
    let mut a5 = [3, 2, 3, 2];
    CheckPre_sort(&a5, 0, 4);
    sort(&mut a5, 0, 4);

    // --- Test Case 8: Boundary - Empty range ---
    let mut a8 = [1, 2, 3, 4];
    CheckPre_sort(&a8, 2, 2);
    sort(&mut a8, 2, 2);

    // --- Test Case 9: Boundary - Single element range ---
    let mut a9 = [10, 42, 20];
    CheckPre_sort(&a9, 1, 2); 
    sort(&mut a9, 1, 2);
}

fn invalid_test_harness_sort() {
    // --- Test Case 6: Invalid - beg > end ---
    // Violates: requires beg <= end
    let mut a6 = [1, 2, 3];
    let (beg6, end6) = (3, 2);
    CheckPre_sort(&a6, beg6, end6);

    // --- Test Case 7: Invalid - array too small ---
    // Violates: requires \valid(a+(beg .. end-1))
    // Trying to sort up to index 3 on an array of length 2
    let mut a7 = [1, 2];
    let (beg7, end7) = (0, 3);
    
    unsafe {
        // Use raw parts to bypass Rust's safe slice bounds for the checker
        let ptr = a7.as_ptr();
        let fake_slice = std::slice::from_raw_parts(ptr, 2);
        CheckPre_sort(fake_slice, beg7, end7);
    }
}

fn valid_test_harness_min_idx_in() {
    let arr = [10, 2, 33, 2, 55, -5, 100];
    
    // --- Test Case 1: Standard range, min is at the start ---
    let (beg1, end1) = (1, 3); // Range [2, 33], min is 2 at index 1
    CheckPre_min_idx_in(&arr, beg1, end1);
    let result1 = 1;
    CheckPost_min_idx_in(&arr, beg1, end1, result1);
    min_idx_in(&arr, beg1, end1);

    // --- Test Case 2: Standard range, min is at the end ---
    let (beg2, end2) = (0, 2); // Range [10, 2], min is 2 at index 1
    CheckPre_min_idx_in(&arr, beg2, end2);
    let result2 = 1;
    CheckPost_min_idx_in(&arr, beg2, end2, result2);
    min_idx_in(&arr, beg2, end2);

    // --- Test Case 3: Single element range (beg + 1 == end) ---
    let (beg3, end3) = (4, 5); // Range [55]
    CheckPre_min_idx_in(&arr, beg3, end3);
    let result3 = 4;
    CheckPost_min_idx_in(&arr, beg3, end3, result3);
    min_idx_in(&arr, beg3, end3);

    // --- Test Case 4: Range contains negative values ---
    let (beg4, end4) = (0, 7); // Full array, min is -5 at index 5
    CheckPre_min_idx_in(&arr, beg4, end4);
    let result4 = 5;
    CheckPost_min_idx_in(&arr, beg4, end4, result4);
    min_idx_in(&arr, beg4, end4);

    // --- Test Case 5: Duplicate minimum values ---
    // Should return the first index of the minimum (based on 'a[i] < a[min_i]')
    let (beg5, end5) = (1, 5); // Range [2, 33, 2, 55], min is 2 at index 1 and 3
    CheckPre_min_idx_in(&arr, beg5, end5);
    let result5 = 1; 
    CheckPost_min_idx_in(&arr, beg5, end5, result5);
    min_idx_in(&arr, beg5, end5);

    // --- Test Case 6: Boundary - end of the physical array ---
    let (beg6, end6) = (5, 7); // Range [-5, 100]
    CheckPre_min_idx_in(&arr, beg6, end6);
    let result6 = 5;
    CheckPost_min_idx_in(&arr, beg6, end6, result6);
    min_idx_in(&arr, beg6, end6);

    // --- Test Case 7: Large sub-range ---
    let (beg7, end7) = (0, 6); // Range [10, 2, 33, 2, 55, -5]
    CheckPre_min_idx_in(&arr, beg7, end7);
    let result7 = 5;
    CheckPost_min_idx_in(&arr, beg7, end7, result7);
    min_idx_in(&arr, beg7, end7);
}

fn invalid_test_harness_min_idx_in() {
    let arr = [1, 2, 3];

    // --- Test Case 8: Violates 'requires beg < end' ---
    // If beg == end, the loop logic or precondition fails
    let (beg8, end8) = (2, 2);
    CheckPre_min_idx_in(&arr, beg8, end8);

    // --- Test Case 9: Violates '\valid_read' (Out of Bounds) ---
    // Accessing index 10 in an array of size 3
    unsafe {
        let (beg9, end9) = (0, 10);
        let raw_ptr = arr.as_ptr();
        // Simulating the passing of an invalid slice length to the checker
        CheckPre_min_idx_in(std::slice::from_raw_parts(raw_ptr, 3), beg9, end9);
    }
}

fn valid_test_harness_swap() {
    // --- Test Case 1: Distinct variables ---
    let (mut a1, mut b1) = (10, 20);
    CheckPre_swap(&mut a1, &mut b1);

    // --- Test Case 2 ---
    let (mut a3, mut b3) = (-100, -214400);
    CheckPre_swap(&mut a3, &mut b3);

    // --- Test Case 3: Identical values ---
    let (mut a3, mut b3) = (42, 42);
    CheckPre_swap(&mut a3, &mut b3);

    // --- Test Case 4: Negative values ---
    let (mut a4, mut b4) = (-1, 5);
    CheckPre_swap(&mut a4, &mut b4);

    // --- Test Case 5: Extreme values (i32::MAX/MIN) ---
    let (mut a5, mut b5) = (2147483647, -2147483648);
    CheckPre_swap(&mut a5, &mut b5);

    // --- Test Case 6: Heap memory (Box) ---
    let mut p6 = Box::new(100);
    let mut q6 = Box::new(200);
    CheckPre_swap(&mut *p6, &mut *q6);

    // --- Test Case 7: Heap memory (Box) ---
    let mut p7 = Box::new(-5);
    let mut q7 = Box::new(20);
    CheckPre_swap(&mut *p7, &mut *q7);
}

fn invalid_test_harness_swap() {
    // --- Test Case 8: Invalid - p is NULL ---
    // Violates: requires \valid(p)
    unsafe {
        let mut b8 = 42;
        let null_p: *mut i32 = std::ptr::null_mut();
        CheckPre_swap(&mut *null_p, &mut b8);
    }

    // --- Test Case 9: Invalid - q is an unaligned or junk address ---
    // Violates: requires \valid(q)
    unsafe {
        let mut a9 = 24;
        let junk_q = 0x1 as *mut i32;
        CheckPre_swap(&mut a9, &mut *junk_q);
    }
}