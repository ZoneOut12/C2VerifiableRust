struct vector<'a> {
    n: i32,
    v: &'a mut [i32],
}

fn CheckPost_predicate(v: i32, result: bool)
{
    assert!(result == (0 != 0) || result == (1 != 0));
}

fn predicate(v: i32) -> bool
{
    v % 2 == 0
}

fn CheckPre_index_where<'a>(old_a: &vector<'a>, old_o: &vector<'a>)
{
    assert!(
        (old_a.v).len() - (((0) as usize)..((old_a.n - 1) as usize)).len() >= 1 &&
        (old_o.v).len() - (((0) as usize)..((old_a.n - 1) as usize)).len() >= 1 &&
        (0..old_a.n).all(|i|
            (0.. old_a.n).all(|j| true)
        ) &&
        old_a.n > 0
    );
}

fn CheckPost_index_where<'a>(a: &vector<'a>, o: &vector<'a>)
{
    assert!(
        0 <= o.n && o.n <= a.n &&
        (0..o.n).all(|i| 0 <= o.v[(i) as usize] && o.v[(i) as usize] < a.n) &&
        (1..o.n).all(|i| o.v[(i - 1) as usize] < o.v[(i) as usize])
    );
}

fn index_where<'a>(a: &mut vector<'a>, o: &mut vector<'a>)
{
    let n: i32 = a.n;
    o.n = 0;

    let mut i: i32 = 0;
    while i < n
    {
        let old_measure = n - i;
        assert!(
            n == a.n &&
            0 <= i && i <= n &&
            0 <= o.n && o.n <= i &&
            (0..o.n).all(|j| 0 <= o.v[(j) as usize] && o.v[(j) as usize] < i) &&
            (1..o.n).all(|j| o.v[(j - 1) as usize] < o.v[(j) as usize])
        );
        if predicate(a.v[i as usize]) {
            o.v[o.n as usize] = i;
            o.n += 1;
        }
        i += 1;
        assert!(old_measure > n - i);
    }
    assert!(
        n == a.n &&
        0 <= i && i <= n &&
        0 <= o.n && o.n <= i &&
        (0..o.n).all(|j| 0 <= o.v[(j) as usize] && o.v[(j) as usize] < i) &&
        (1..o.n).all(|j| o.v[(j - 1) as usize] < o.v[(j) as usize])
    );
}

fn main() {
    valid_test_harness_predicate();
    valid_test_harness_index_where();
    // invalid_test_harness_index_where();
}

fn valid_test_harness_predicate() {
    // --- Test Case 1: Positive even number ---
    // 2 % 2 == 0 -> returns 1
    let v1 = 2;
    let result1 = 1;
    CheckPost_predicate(v1, result1 != 0);

    // --- Test Case 2: Positive odd number ---
    // 3 % 2 == 1 -> returns 0
    let v2 = 3;
    let result2 = 0;
    CheckPost_predicate(v2, result2 != 0);

    // --- Test Case 3: Zero (treated as even) ---
    // 0 % 2 == 0 -> returns 1
    let v3 = 0;
    let result3 = 1;
    CheckPost_predicate(v3, result3 != 0);

    // --- Test Case 4: Negative even number ---
    // -4 % 2 == 0 -> returns 1
    let v4 = -4;
    let result4 = 1;
    CheckPost_predicate(v4, result4 != 0);

    // --- Test Case 5: Negative odd number ---
    // -5 % 2 == -1 (in C), which is != 0 -> returns 0
    let v5 = -5;
    let result5 = 0;
    CheckPost_predicate(v5, result5 != 0);

    // --- Test Case 6: Maximum positive integer (Odd) ---
    let v6 = i32::MAX; // 2147483647
    let result6 = 0;
    CheckPost_predicate(v6, result6 != 0);

    // --- Test Case 7: Minimum negative integer (Even) ---
    let v7 = i32::MIN; // -2147483648
    let result7 = 1;
    CheckPost_predicate(v7, result7 != 0);
}

fn valid_test_harness_index_where() {
    let mut ov_buf = [0i32; 10];

    // --- Test Case 1: All elements match (All Even) ---
    let mut av1 = [2, 4, 6];
    let a1 = vector { n: 3, v: &mut av1 };
    let mut o1 = vector { n: 0, v: &mut ov_buf[..3] };
    CheckPre_index_where(&a1, &o1);
    // After logic execution: o.n = 3, o.v = [0, 1, 2]
    o1.n = 3; o1.v[0] = 0; o1.v[1] = 1; o1.v[2] = 2;
    CheckPost_index_where(&a1, &o1);

    // --- Test Case 2: Mixed elements ---
    let mut av2 = [1, 2, 3];
    let a2 = vector { n: 3, v: &mut av2 };
    let mut o2 = vector { n: 0, v: &mut ov_buf[..3] };
    CheckPre_index_where(&a2, &o2);
    // After logic: only index 1 (value 2) is even
    o2.n = 1; o2.v[0] = 1;
    CheckPost_index_where(&a2, &o2);

    // --- Test Case 3: No matches (All Odd) ---
    let mut av3 = [1, 3, 5];
    let a3 = vector { n: 3, v: &mut av3 };
    let mut o3 = vector { n: 0, v: &mut ov_buf[..3] };
    CheckPre_index_where(&a3, &o3);
    // After logic: o.n = 0
    o3.n = 0;
    CheckPost_index_where(&a3, &o3);

    // --- Test Case 4: Alternating pattern with zero ---
    let mut av4 = [0, 1, 2, 3, 4];
    let a4 = vector { n: 5, v: &mut av4 };
    let mut o4 = vector { n: 0, v: &mut ov_buf[..5] };
    CheckPre_index_where(&a4, &o4);
    // After logic: indices [0, 2, 4] are even
    o4.n = 3; o4.v[0] = 0; o4.v[1] = 2; o4.v[2] = 4;
    CheckPost_index_where(&a4, &o4);

    // --- Test Case 5: Single element match ---
    let mut av5 = [8];
    let a5 = vector { n: 1, v: &mut av5 };
    let mut o5 = vector { n: 0, v: &mut ov_buf[..1] };
    CheckPre_index_where(&a5, &o5);
    o5.n = 1; o5.v[0] = 0;
    CheckPost_index_where(&a5, &o5);

    // --- Test Case 8: Boundary - Minimum size with match ---
    let mut av8 = [0];
    let a8 = vector { n: 1, v: &mut av8 };
    let mut o8 = vector { n: 0, v: &mut ov_buf[..1] };
    CheckPre_index_where(&a8, &o8);
    o8.n = 1; o8.v[0] = 0;
    CheckPost_index_where(&a8, &o8);

    // --- Test Case 9: Boundary - Minimum size no match ---
    let mut av9 = [7];
    let a9 = vector { n: 1, v: &mut av9 };
    let mut o9 = vector { n: 0, v: &mut ov_buf[..1] };
    CheckPre_index_where(&a9, &o9);
    o9.n = 0;
    CheckPost_index_where(&a9, &o9);
}

fn invalid_test_harness_index_where() {
    let mut ov_buf = [0i32; 5];

    // --- Test Case 6: Invalid - NULL input simulation ---
    // Violates: requires \valid(a)
    unsafe {
        let null_vec: *const vector = std::ptr::null();
        let mut o_valid = vector { n: 0, v: &mut ov_buf };
        CheckPre_index_where(&*null_vec, &o_valid);
    }

    // --- Test Case 7: Invalid - size n is 0 ---
    // Violates: requires a->n > 0
    let mut av7 = [10, 20];
    let a7 = vector { n: 0, v: &mut av7 };
    let mut o7 = vector { n: 0, v: &mut ov_buf[..2] };
    CheckPre_index_where(&a7, &o7);
}