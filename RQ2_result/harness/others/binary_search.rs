#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

fn CheckPre_binsearch(base: &[i32], n: i32, key: i32)
    requires
        n >= 0,
        base@.len() >= n - 1 + 1,
        forall|k1: int, k2: int|
            (0 <= k1 < k2 < n) as int != 0 ==> (base@[(k1) as int] <= base@[(k2) as int]) as int
                != 0,
{}

fn CheckPost_binsearch(base: &[i32], n: i32, key: i32, result: i32)
    requires
        result >= -1 && result < n,
        (exists|k: int| 0 <= k < n && base@[(k) as int] == key) ==> (base@[(result) as int] == key),
        (forall|k: int| (0 <= k < n) as int != 0 ==> (base@[(k) as int] != key) as int != 0) ==> (
        result == -1),
{}

#[verifier::external_body]
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn binsearch(base: &[i32], n: i32, key: i32) -> (result: i32)
    requires
        n >= 0,
        base@.len() >= n - 1 + 1,
        forall|k1: int, k2: int|
            (0 <= k1 < k2 < n) as int != 0 ==> (base@[(k1) as int] <= base@[(k2) as int]) as int
                != 0,
    ensures
        result >= -1 && result < n,
        (exists|k: int| 0 <= k < n && base@[(k) as int] == key) ==> (base@[(result) as int] == key),
        (forall|k: int| (0 <= k < n) as int != 0 ==> (base@[(k) as int] != key) as int != 0) ==> (
        result == -1),
{
    let mut l: i32 = 0;
    let mut h: i32 = n - 1;

    while l <= h
        invariant
            0 <= l,
            h < n,
            forall|i: int|
                (0 <= i < n && base@[(i) as int] == key) as int != 0 ==> (l <= i <= h) as int != 0,
        decreases h - l,
    {
        let m: i32 = l + (h - l) / 2;
        let val: i32 = base[m as usize];

        if val < key {
            l = m + 1;
            assert(forall|k1: int, k2: int|
                (0 <= k1 < k2 < l) as int != 0 ==> (base@[(k1) as int] <= base@[(k2) as int]) as int
                    != 0);
            assert(base@[(m) as int] < key && m == l - 1);
        } else if val > key {
            h = m - 1;
        } else {
            assert(forall|i: int|
                (0 <= i < n && base@[(i) as int] == key) as int != 0 ==> (l <= i <= h) as int != 0);
            return m;
        }
    }

    -1
}

fn main() {
}

fn valid_test_harness_binsearch() {
    // --- Test Case 1: Key in middle ---
    let arr1 = [1, 2, 3, 4, 5];
    let key1 = 3;
    CheckPre_binsearch(&arr1, arr1.len() as i32, key1);
    let result1 = 2; // Index of 3
    CheckPost_binsearch(&arr1, arr1.len() as i32, key1, result1);

    // --- Test Case 2: Key not present ---
    let arr2 = [1, 2, 3, 4, 5];
    let key2 = 6;
    CheckPre_binsearch(&arr2, arr2.len() as i32, key2);
    let result2 = -1;
    CheckPost_binsearch(&arr2, arr2.len() as i32, key2, result2);

    // --- Test Case 3: Single element present ---
    let arr3 = [42];
    let key3 = 42;
    CheckPre_binsearch(&arr3, arr3.len() as i32, key3);
    let result3 = 0;
    CheckPost_binsearch(&arr3, arr3.len() as i32, key3, result3);

    // --- Test Case 4: Single element NOT present (The missing case) ---
    let arr4 = [42];
    let key4 = 5;
    CheckPre_binsearch(&arr4, arr4.len() as i32, key4);
    let result4 = -1;
    CheckPost_binsearch(&arr4, arr4.len() as i32, key4, result4);

    // --- Test Case 5: Key at start ---
    let arr5 = [10, 20, 30];
    let key5 = 10;
    CheckPre_binsearch(&arr5, arr5.len() as i32, key5);
    let result5 = 0;
    CheckPost_binsearch(&arr5, arr5.len() as i32, key5, result5);

    // --- Test Case 8: Boundary - empty array ---
    let arr8: [i32; 0] = [];
    let key8 = 5;
    CheckPre_binsearch(&arr8, 0, key8);
    let result8 = -1;
    CheckPost_binsearch(&arr8, 0, key8, result8);

    // --- Test Case 9: Boundary - key at end ---
    let arr9 = [5, 6, 7];
    let key9 = 7;
    CheckPre_binsearch(&arr9, arr9.len() as i32, key9);
    let result9 = 2;
    CheckPost_binsearch(&arr9, arr9.len() as i32, key9, result9);
}

fn invalid_test_harness_binsearch() {
    // --- Test Case 6: Invalid n (Violates n >= 0) ---
    let arr6 = [1, 2, 3];
    CheckPre_binsearch(&arr6, -2, 2);

    // --- Test Case 7: Invalid - Unsorted (Violates base[k1] <= base[k2]) ---
    let arr7 = [3, 1, 2];
    CheckPre_binsearch(&arr7, 3, 2);
}

} // verus!


// RAC
// fn binsearch(base: &[i32], n: i32, key: i32) -> i32
// {
//     let mut l: i32 = 0;
//     let mut h: i32 = n - 1;

//     while l <= h
//     {
//         let old_measure = h - l;
//         assert!(
//             0 <= l &&
//             h < n &&
//             (0..n).all(|i| !(base[(i) as usize] == key) || (l <= i && i <= h))
//         );
//         let m: i32 = l + (h - l) / 2;
//         let val: i32 = base[m as usize];

//         if val < key {
//             l = m + 1;
//             assert!(
//                 (0..l-1).all(|k1|
//                     (k1..l).all(|k2| base[(k1) as usize] <= base[(k2) as usize])
//                 )
//             );
//             assert!(base[(m) as usize] < key && m == l - 1);
//         } else if val > key {
//             h = m - 1;
//         } else {
//             assert!(
//                 (0..n).all(|i| !(base[(i) as usize] == key) || (l <= i && i <= h))
//             );
//             return m;
//         }
//         assert!(old_measure > h - l);
//     }
//     assert!(
//         0 <= l &&
//         h < n &&
//         (0..n).all(|i| !(base[(i) as usize] == key) || (l <= i && i <= h))
//     );
//     -1
// }

// fn main() {
//     valid_test_harness_binsearch();
// }

// fn valid_test_harness_binsearch() {
//     // --- Test Case 1: Key in middle ---
//     let arr1 = [1, 2, 3, 4, 5];
//     let key1 = 3;
//     binsearch(&arr1, arr1.len() as i32, key1);

//     // --- Test Case 2: Key not present ---
//     let arr2 = [1, 2, 3, 4, 5];
//     let key2 = 6;
//     binsearch(&arr2, arr2.len() as i32, key2);

//     // --- Test Case 3: Single element present ---
//     let arr3 = [42];
//     let key3 = 42;
//     binsearch(&arr3, arr3.len() as i32, key3);

//     // --- Test Case 4: Single element NOT present (The missing case) ---
//     let arr4 = [42];
//     let key4 = 5;
//     binsearch(&arr4, arr4.len() as i32, key4);

//     // --- Test Case 5: Key at start ---
//     let arr5 = [10, 20, 30];
//     let key5 = 10;
//     binsearch(&arr5, arr5.len() as i32, key5);

//     // --- Test Case 8: Boundary - empty array ---
//     let arr8: [i32; 0] = [];
//     let key8 = 5;
//     binsearch(&arr8, 0, key8);

//     // --- Test Case 9: Boundary - key at end ---
//     let arr9 = [5, 6, 7];
//     let key9 = 7;
//     binsearch(&arr9, arr9.len() as i32, key9);
// }