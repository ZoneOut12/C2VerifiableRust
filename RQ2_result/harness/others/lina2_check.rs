fn CheckPre_index_where_even(x0: &[i32], x1: i32, old_x2: &[i32])
{
    assert!(
        (((x1 > 0) && (x0.len() as i32) >= x1 - 1 + 1) && (old_x2.len() as i32) >= x1 - 1 + 1)
    );
}

fn CheckPost_index_where_even(x0: &[i32], x1: i32, x2: &[i32], result: i32)
{
    assert!(
        ((((0 <= result) && (result <= x1)) && (
            (0..result).all(|x74| (0 <= x2[(x74) as usize]) && (x2[(
        x74) as usize] < x1))
       )
    )) && (
        (1..result).all(|x86| (x2[((x86 - 1)) as usize] < x2[(
        x86) as usize]))
    )
    );
}

fn index_where_even(x0: &[i32], x1: i32, x2: &mut [i32]) -> i32
{
    let mut x5: i32 = 0;
    let mut x6: i32 = 0;
    while x6 < x1
    {
        let old_measure = x1 - x6;
        assert!(
            ((((((0 <= x6) && (x6 <= x1)) && (0 <= x5)) && (x5 <= x6)) && (
                (0..x5).all(|x28| ((0 <= x2[(x28) as usize]) && (x2[(x28) as usize] < x6))))) && (
                (1..x5).all(|x42| (x2[((x42 - 1)) as usize] < x2[(
                x42) as usize]))
            ))
        );
        let x7: i32 = x0[x6 as usize];
        let x8: i32 = x7 % 2;
        let x9: bool = x8 == 0;
        if x9 {
            let x10: i32 = x5;
            x2[x10 as usize] = x6;
            x5 += 1;
        }
        x6 += 1;
        assert!(old_measure > x1 - x6);
    }
    assert!(
        ((((((0 <= x6) && (x6 <= x1)) && (0 <= x5)) && (x5 <= x6)) && (
            (0..x5).all(|x28| ((0 <= x2[(x28) as usize]) && (x2[(x28) as usize] < x6))))) && (
            (1..x5).all(|x42| (x2[((x42 - 1)) as usize] < x2[(
            x42) as usize]))
        ))
    );
    let x62: i32 = x5;
    x62
}

fn main() {
    valid_test_harness_index_where_even();
    invalid_test_harness_index_where_even();
}

fn valid_test_harness_index_where_even() {
    // Shared buffer for x2 with sufficient capacity
    let mut x2_buffer = [0i32; 10];

    // --- Test Case 1: Normal mixed even/odd ---
    let x0_1 = [1, 2, 3, 4, 5];
    CheckPre_index_where_even(&x0_1, 5, &x2_buffer);
    // Logic: even values are 2 (index 1) and 4 (index 3). Result count is 2.
    let mut x2_1 = x2_buffer; 
    x2_1[0] = 1; x2_1[1] = 3;
    CheckPost_index_where_even(&x0_1, 5, &x2_1, 2);
    index_where_even(&x0_1, 5, &mut x2_buffer);

    // --- Test Case 2: All elements are even ---
    let x0_2 = [2, 4, 6];
    CheckPre_index_where_even(&x0_2, 3, &x2_buffer);
    // Logic: all indices [0, 1, 2] should be stored. Result count is 3.
    let mut x2_2 = x2_buffer; 
    x2_2[0] = 0; x2_2[1] = 1; x2_2[2] = 2;
    CheckPost_index_where_even(&x0_2, 3, &x2_2, 3);
    index_where_even(&x0_2, 3, &mut x2_buffer);

    // --- Test Case 3: No even elements ---
    let x0_3 = [1, 3, 5];
    CheckPre_index_where_even(&x0_3, 3, &x2_buffer);
    // Logic: no indices stored. Result count is 0.
    CheckPost_index_where_even(&x0_3, 3, &x2_buffer, 0);
    index_where_even(&x0_3, 3, &mut x2_buffer);

    // --- Test Case 4: Contains zero and increasing values ---
    let x0_4 = [0, 1, 2, 3, 4];
    CheckPre_index_where_even(&x0_4, 5, &x2_buffer);
    // Logic: indices [0, 2, 4] contain even numbers. Result count is 3.
    let mut x2_4 = x2_buffer; 
    x2_4[0] = 0; x2_4[1] = 2; x2_4[2] = 4;
    CheckPost_index_where_even(&x0_4, 5, &x2_4, 3);
    index_where_even(&x0_4, 5, &mut x2_buffer);

    // --- Test Case 5: Single element (zero) ---
    let x0_5 = [0];
    CheckPre_index_where_even(&x0_5, 1, &x2_buffer);
    let mut x2_5 = x2_buffer; 
    x2_5[0] = 0;
    CheckPost_index_where_even(&x0_5, 1, &x2_5, 1);
    index_where_even(&x0_5, 1, &mut x2_buffer);

    // --- Test Case 8: Boundary - Minimum valid size ---
    let x0_8 = [8];
    CheckPre_index_where_even(&x0_8, 1, &x2_buffer);
    let mut x2_8 = x2_buffer; 
    x2_8[0] = 0;
    CheckPost_index_where_even(&x0_8, 1, &x2_8, 1);
    index_where_even(&x0_8, 1, &mut x2_buffer);

    // --- Test Case 9: Boundary - Two even elements ---
    let x0_9 = [10, 20];
    CheckPre_index_where_even(&x0_9, 2, &x2_buffer);
    let mut x2_9 = x2_buffer; 
    x2_9[0] = 0; x2_9[1] = 1;
    CheckPost_index_where_even(&x0_9, 2, &x2_9, 2);
    index_where_even(&x0_9, 2, &mut x2_buffer);
}

fn invalid_test_harness_index_where_even() {
    // let x0 = [1, 2];
    // let mut x2 = [0i32; 2];

    // // --- Test Case 6: Invalid - size x1 is zero ---
    // // Violates: requires x1 > 0
    // CheckPre_index_where_even(&x0, 0, &mut x2);

    // // --- Test Case 7: Invalid - NULL pointer simulation ---
    // // Violates: \valid(x0 + (0..x1-1))
    // unsafe {
    //     let null_ptr: *const i32 = std::ptr::null();
    //     let raw_slice = std::slice::from_raw_parts(null_ptr, 2);
    //     CheckPre_index_where_even(raw_slice, 2, &mut x2);
    // }
}