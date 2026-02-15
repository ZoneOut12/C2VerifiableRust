// #[allow(unused_imports)]
// use vstd::math::*;
// use vstd::prelude::*;
// use vstd::slice::*;
// verus! {

// fn CheckPre_arrayDouble(old_a: &[i32], n: i32)
//     requires
//         n > 0,
//         old_a@.len() >= n - 1 + 1,
//         forall|k: int|
//             (0 <= k < n) as int != 0 ==> (old_a@[(k) as int] == k && 2 * k <= i32::MAX) as int
//                 != 0,
// {}

// fn CheckPost_arrayDouble(a: &[i32], n: i32)
//     requires
//         forall|k: int| (0 <= k < n) as int != 0 ==> (a@[(k) as int] == 2 * k) as int != 0,
// {}


// #[verifier::external_body]
// #[verifier::loop_isolation(false)]
// #[verifier::exec_allows_no_decreases_clause]
// fn arrayDouble(a: &mut [i32], n: i32)
//     requires
//         n > 0,
//         old(a)@.len() >= n - 1 + 1,
//         forall|k: int|
//             (0 <= k < n) as int != 0 ==> (old(a)@[(k) as int] == k && 2 * k <= i32::MAX) as int
//                 != 0,
//     ensures
//         forall|k: int| (0 <= k < n) as int != 0 ==> (a@[(k) as int] == 2 * k) as int != 0,
// {
//     let mut p: i32 = 0;
//     while p < n
//         invariant
//             0 <= p <= n,
//             forall|k: int| (p <= k < n) as int != 0 ==> (a@[(k) as int] == k) as int != 0,
//             forall|k: int| (0 <= k < p) as int != 0 ==> (a@[(k) as int] == 2 * k) as int != 0,
//         decreases n - p,
//     {
//         a[p as usize] = a[p as usize] * 2;
//         p = p + 1;
//     }
// }

// #[verifier::loop_isolation(false)]
// #[verifier::exec_allows_no_decreases_clause]
// fn main() {
//     let mut arr: [i32; 6] = [0, 1, 2, 3, 4, 5];
//     // arrayDouble(&mut arr, 6);
// }

// fn valid_test_harness_array_double() {
//     // Test case 1: Valid - normal array
//     let mut arr1 = [0, 1, 2, 3, 4];
//     let n1 = 5;
//     CheckPre_arrayDouble(&arr1, n1);
//     let new_arr1 = [0, 2, 4, 6, 8];
//     CheckPost_arrayDouble(&new_arr1, n1);

//     // Test case 2: Valid - minimum n=1
//     let mut arr2 = [0];
//     let n2 = 1;
//     CheckPre_arrayDouble(&arr2, n2);
//     let new_arr2 = [0];
//     CheckPost_arrayDouble(&new_arr2, n2);

//     // --- Test Case 3: Valid - length 2 (n=2) ---
//     let arr3 = [0, 1];
//     let n3 = 2;
//     CheckPre_arrayDouble(&arr3, n3);
//     let new_arr3 = [0, 2];
//     CheckPost_arrayDouble(&new_arr3, n3);

//     // --- Test Case 4: Valid - length 3 (n=3) ---
//     let arr4 = [0, 1, 2];
//     let n4 = 3;
//     CheckPre_arrayDouble(&arr4, n4);
//     let new_arr4 = [0, 2, 4];
//     CheckPost_arrayDouble(&new_arr4, n4);

//     // Test case 5: Valid - original example
//     let mut arr5 = [0, 1, 2, 3, 4, 5];
//     let n5 = 6;
//     CheckPre_arrayDouble(&arr5, n5);
//     let new_arr5 = [0, 2, 4, 6, 8, 10];
//     CheckPost_arrayDouble(&new_arr5, n5);

//     // Test case 8/9: Boundary cases
//     let mut arr8 = [0, 1];
//     let n8 = 2;
//     CheckPre_arrayDouble(&arr8, n8);
//     let new_arr8 = [0, 2];
//     CheckPost_arrayDouble(&new_arr8, n8);

//     // --- Test Case 9: Boundary - n=2 ---
//     let arr9 = [0, 1];
//     let n9 = 2;
//     CheckPre_arrayDouble(&arr9, n9);
//     let new_arr9 = [0, 2];
//     CheckPost_arrayDouble(&new_arr9, n9);
// }

// fn invalid_test_harness_array_double() {
//     // --- Test Case 6: Invalid - n=0 (Violates: n > 0) ---
//     let arr6 = [0, 1];
//     CheckPre_arrayDouble(&arr6, 0);

//     // --- Test Case 7: Invalid - Content mismatch (Violates: a[k] == k) ---
//     let arr7 = [1, 2]; // Should be [0, 1]
//     CheckPre_arrayDouble(&arr7, 2);
// }

// } // verus!


// RAC
fn arrayDouble(a: &mut [i32], n: i32)
{
    let mut p: i32 = 0;
    while p < n
    {
        let old_measure = n - p;
        assert!(
            0 <= p && p <= n &&
            (p..n).all(|k| a[(k) as usize] == k) &&
            (0..p).all(|k| a[(k) as usize] == 2 * k)
        );
        a[p as usize] = a[p as usize] * 2;
        p = p + 1;
        assert!(old_measure > n - p);
    }
    assert!(
        0 <= p && p <= n &&
        (p..n).all(|k| a[(k) as usize] == k) &&
        (0..p).all(|k| a[(k) as usize] == 2 * k)
    );
}

fn main() {
    valid_test_harness_array_double();

    let mut arr: [i32; 6] = [0, 1, 2, 3, 4, 5];
    arrayDouble(&mut arr, 6);
}

fn valid_test_harness_array_double() {
    // Test case 1: Valid - normal array
    let mut arr1 = [0, 1, 2, 3, 4];
    let n1 = 5;
    arrayDouble(&mut arr1, n1);

    // Test case 2: Valid - minimum n=1
    let mut arr2 = [0];
    let n2 = 1;
    arrayDouble(&mut arr2, n2);

    // --- Test Case 3: Valid - length 2 (n=2) ---
    let mut arr3 = [0, 1];
    let n3 = 2;
    arrayDouble(&mut arr3, n3);

    // --- Test Case 4: Valid - length 3 (n=3) ---
    let mut arr4 = [0, 1, 2];
    let n4 = 3;
    arrayDouble(&mut arr4, n4);

    // Test case 5: Valid - original example
    let mut arr5 = [0, 1, 2, 3, 4, 5];
    let n5 = 6;
    arrayDouble(&mut arr5, n5);

    // Test case 8/9: Boundary cases
    let mut arr8 = [0, 1];
    let n8 = 2;
    arrayDouble(&mut arr8, n8);

    // --- Test Case 9: Boundary - n=2 ---
    let mut arr9 = [0, 1];
    let n9 = 2;
    arrayDouble(&mut arr9, n9);
}