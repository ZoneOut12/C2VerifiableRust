#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

fn CheckPost_predicate(v: i32, result: bool)
    requires
        result == (0 != 0) || result == (1 != 0),
{}

#[verifier::external_body]
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn predicate(v: i32) -> (result: bool)
    ensures
        result == (0 != 0) || result == (1 != 0),
{
    v % 2 == 0
}

fn CheckPre_index_where(v: &[i32], n: i32, old_o: &[i32])
    requires
        n > 0,
        v@.len() >= n - 1 + 1,
        old_o@.len() >= n - 1 + 1,
{}

fn CheckPost_index_where(v: &[i32], n: i32, o: &[i32], result: i32)
    requires
        0 <= result <= n,
        forall|i: i32| (0 <= i < result) as int != 0 ==> (0 <= #[trigger] o@[(i) as int] < n) as int != 0,
        forall|i: i32|
            (0 < i < result) as int != 0 ==> (o@[(i - 1) as int] < #[trigger] o@[(i) as int]) as int != 0,
{}

#[verifier::external_body]
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn index_where(v: &[i32], n: i32, o: &mut [i32]) -> (result: i32)
    requires
        n > 0,
        v@.len() >= n - 1 + 1,
        old(o)@.len() >= n - 1 + 1,
    ensures
        0 <= result <= n,
        forall|i: i32| (0 <= i < result) as int != 0 ==> (0 <= #[trigger] o@[(i) as int] < n) as int != 0,
        forall|i: i32|
            (0 < i < result) as int != 0 ==> (o@[(i - 1) as int] < #[trigger] o@[(i) as int]) as int != 0,
{
    let mut r: i32 = 0;
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            0 <= r <= i,
            forall|j: i32| (0 <= j < r) as int != 0 ==> (0 <= o@[(j) as int] < i) as int != 0,
            forall|j: i32|
                (0 < j < r) as int != 0 ==> (o@[(j - 1) as int] < o@[(j) as int]) as int != 0,
        decreases n - i,
    {
        if predicate(v[i as usize]) {
            o[r as usize] = i;
            r += 1;
        }
        i += 1;
    }
    r
}

fn main() {
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
    // --- Test Case 1: All elements match ---
    let av1 = [2, 4, 6];
    let mut ov1 = [0i32; 3];
    CheckPre_index_where(&av1, 3, &ov1);
    // Expected: result = 3, indices = [0, 1, 2]
    ov1[0] = 0; ov1[1] = 1; ov1[2] = 2;
    CheckPost_index_where(&av1, 3, &ov1, 3);

    // --- Test Case 2: Mixed elements ---
    let av2 = [1, 2, 3];
    let mut ov2 = [0i32; 3];
    CheckPre_index_where(&av2, 3, &ov2);
    // Expected: result = 1, indices = [1] (value 2 is at index 1)
    ov2[0] = 1;
    CheckPost_index_where(&av2, 3, &ov2, 1);

    // --- Test Case 3: No matches ---
    let av3 = [1, 3, 5];
    let mut ov3 = [0i32; 3];
    CheckPre_index_where(&av3, 3, &ov3);
    // Expected: result = 0
    CheckPost_index_where(&av3, 3, &ov3, 0);

    // --- Test Case 4: Alternating pattern ---
    let av4 = [0, 1, 2, 3, 4];
    let mut ov4 = [0i32; 5];
    CheckPre_index_where(&av4, 5, &ov4);
    // Expected: result = 3, indices = [0, 2, 4]
    ov4[0] = 0; ov4[1] = 2; ov4[2] = 4;
    CheckPost_index_where(&av4, 5, &ov4, 3);

    // --- Test Case 5: Single element match ---
    let av5 = [2];
    let mut ov5 = [0i32; 1];
    CheckPre_index_where(&av5, 1, &ov5);
    ov5[0] = 0;
    CheckPost_index_where(&av5, 1, &ov5, 1);

    // --- Test Case 8: Boundary - Minimum size with match ---
    let av8 = [2];
    let mut ov8 = [0i32; 1];
    CheckPre_index_where(&av8, 1, &ov8);
    ov8[0] = 0;
    CheckPost_index_where(&av8, 1, &ov8, 1);

    // --- Test Case 9: Boundary - Minimum size no match ---
    let av9 = [1];
    let mut ov9 = [0i32; 1];
    CheckPre_index_where(&av9, 1, &ov9);
    CheckPost_index_where(&av9, 1, &ov9, 0);
}

fn invalid_test_harness_index_where() {
    // let av = [1, 2];
    // let ov = [0i32; 2];

    // // --- Test Case 6: Invalid - NULL input simulation ---
    // unsafe {
    //     CheckPre_index_where(None, 3, &ov);
    // }

    // // --- Test Case 7: Invalid - size n is 0 ---
    // CheckPre_index_where(&av, 0, &ov);
}

} // verus!

// RAC
// fn predicate(v: i32) -> bool
// {
//     v % 2 == 0
// }

// fn index_where(v: &[i32], n: i32, o: &mut [i32]) -> i32
// {
//     let mut r: i32 = 0;
//     let mut i: i32 = 0;
//     while i < n
//     {
//         let old_measure = n - i;
//         assert!(
//             0 <= i && i <= n &&
//             0 <= r && r <= i &&
//             (0..r).all(|j| 0 <= o[(j) as usize] && o[(j) as usize] < i) &&
//             (1..r).all(|j| o[(j - 1) as usize] < o[(j) as usize])
//         );
//         if predicate(v[i as usize]) {
//             o[r as usize] = i;
//             r += 1;
//         }
//         i += 1;
//         assert!(old_measure > n - i)
//     }
//     assert!(
//         0 <= i && i <= n &&
//         0 <= r && r <= i &&
//         (0..r).all(|j| 0 <= o[(j) as usize] && o[(j) as usize] < i) &&
//         (1..r).all(|j| o[(j - 1) as usize] < o[(j) as usize])
//     );
//     r
// }

// fn main() {
//     valid_test_harness_index_where();
// }

// fn valid_test_harness_index_where() {
//     // --- Test Case 1: All elements match ---
//     let av1 = [2, 4, 6];
//     let mut ov1 = [0i32; 3];
//     index_where(&av1, 3, &mut ov1);

//     // --- Test Case 2: Mixed elements ---
//     let av2 = [1, 2, 3];
//     let mut ov2 = [0i32; 3];
//     index_where(&av2, 3, &mut ov2);

//     // --- Test Case 3: No matches ---
//     let av3 = [1, 3, 5];
//     let mut ov3 = [0i32; 3];
//     index_where(&av3, 3, &mut ov3);

//     // --- Test Case 4: Alternating pattern ---
//     let av4 = [0, 1, 2, 3, 4];
//     let mut ov4 = [0i32; 5];
//     index_where(&av4, 5, &mut ov4);

//     // --- Test Case 5: Single element match ---
//     let av5 = [2];
//     let mut ov5 = [0i32; 1];
//     index_where(&av5, 1, &mut ov5);

//     // --- Test Case 8: Boundary - Minimum size with match ---
//     let av8 = [2];
//     let mut ov8 = [0i32; 1];
//     index_where(&av8, 1, &mut ov8);

//     // --- Test Case 9: Boundary - Minimum size no match ---
//     let av9 = [1];
//     let mut ov9 = [0i32; 1];
//     index_where(&av9, 1, &mut ov9);
// }