fn CheckPre_func(old_a: &[i32], n: i32)
{
    assert!(
        n > 0 &&
        old_a.len() as i32 >= n - 1 + 1
    );
}

fn CheckPost_func(a: &[i32], n: i32)
{
    assert!(
        (0..n).all(|k| !(k % 2 == 0) || a[(k) as usize] == 0)
    );
}

fn func(a: &mut [i32], n: i32)
{
    let mut i: i32 = 0;
    while i < n
    {
        let old_measure = n - i;
        assert!(
            0 <= i && i <= n &&
            (0..i).all(|k| !(k % 2 == 0) || a[(k) as usize] == 0) && 
            (0..i).all(|k| !(k % 2 == 0) || a[(k) as usize] == a[(k) as usize])
        );
        if i % 2 == 0 {
            a[i as usize] = 0;
        }
        i += 1;
        assert!(old_measure > n - i);
    }
    assert!(
        0 <= i && i <= n &&
        (0..i).all(|k| !(k % 2 == 0) || a[(k) as usize] == 0) && 
        (0..i).all(|k| !(k % 2 == 0) || a[(k) as usize] == a[(k) as usize])
    );
}

fn main() {
    valid_test_harness_func();
    // invalid_test_harness_func();
}

fn valid_test_harness_func() {
    // --- Test Case 1: Mixed values ---
    let mut a1 = [1, 2, 3];
    CheckPre_func(&a1, 3);
    // Logic: a[0]=0, a[2]=0 -> [0, 2, 0]
    let result1 = [0, 2, 0];
    CheckPost_func(&result1, 3);
    func(&mut a1, 3);

    // --- Test Case 2: Single element ---
    let mut a2 = [5];
    CheckPre_func(&a2, 1);
    // Logic: a[0]=0 -> [0]
    let result2 = [0];
    CheckPost_func(&result2, 1);
    func(&mut a2, 1);

    // --- Test Case 3: Negative and zero values ---
    let mut a3 = [0, -1];
    CheckPre_func(&a3, 2);
    // Logic: a[0]=0 -> [0, -1]
    let result3 = [0, -1];
    CheckPost_func(&result3, 2);
    func(&mut a3, 2);

    // --- Test Case 4: Even length array ---
    let mut a4 = [4, 3, 2, 1];
    CheckPre_func(&a4, 4);
    // Logic: a[0]=0, a[2]=0 -> [0, 3, 0, 1]
    let result4 = [0, 3, 0, 1];
    CheckPost_func(&result4, 4);
    func(&mut a4, 4);

    // --- Test Case 5: Odd length with identical values ---
    let mut a5 = [1, 1, 1, 1, 1];
    CheckPre_func(&a5, 5);
    // Logic: indices 0, 2, 4 become 0 -> [0, 1, 0, 1, 0]
    let result5 = [0, 1, 0, 1, 0];
    CheckPost_func(&result5, 5);
    func(&mut a5, 5);

    // --- Test Case 8: Boundary - Minimum size ---
    let mut a8 = [10];
    CheckPre_func(&a8, 1);
    let result8 = [0];
    CheckPost_func(&result8, 1);
    func(&mut a8, 1);

    // --- Test Case 9: Boundary - Size 2 ---
    let mut a9 = [2, 3];
    CheckPre_func(&a9, 2);
    let result9 = [0, 3];
    CheckPost_func(&result9, 2);
    func(&mut a9, 2);
}

fn invalid_test_harness_func() {
    // --- Test Case 6: Invalid - NULL pointer simulation ---
    // CheckPre_func(None, 2);

    // --- Test Case 7: Invalid - Pointer valid but size 'n' is incorrect ---
    // Violates: requires \valid(a + (0..n-1))
    // The array only has 1 element, but we tell the function n=2
    let mut a7_buf = [7];
    CheckPre_func(&mut a7_buf, 2);
}