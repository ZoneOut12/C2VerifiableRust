#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

fn CheckPre_bsearch(arr: &[i32], len: i32, value: i32)
    requires
        arr@.len() >= len - 1 + 1,
        forall|i: int, j: int|
            (0 <= i <= j < len) as int != 0 ==> (arr@[(i) as int] <= arr@[(j) as int]) as int != 0,
        len >= 0,
{}

fn CheckPost_bsearch(arr: &[i32], len: i32, value: i32, result: i32)
    requires
        -1 <= result < len,
        (exists|j: int| 0 <= j < len && arr@[(j) as int] == value) ==> (arr@[(result) as int]
            == value),
        (forall|j: int| (0 <= j < len) as int != 0 ==> (arr@[(j) as int] != value) as int != 0)
            ==> (result == -1),
{}

#[verifier::external_body]
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn bsearch(arr: &[i32], len: i32, value: i32) -> (result: i32)
    requires
        arr@.len() >= len - 1 + 1,
        forall|i: int, j: int|
            (0 <= i <= j < len) as int != 0 ==> (arr@[(i) as int] <= arr@[(j) as int]) as int != 0,
        len >= 0,
    ensures
        -1 <= result < len,
        (exists|j: int| 0 <= j < len && arr@[(j) as int] == value) ==> (arr@[(result) as int]
            == value),
        (forall|j: int| (0 <= j < len) as int != 0 ==> (arr@[(j) as int] != value) as int != 0)
            ==> (result == -1),
{
    if len == 0 {
        return -1;
    }
    let mut low: i32 = 0;
    let mut up: i32 = len - 1;
    while low <= up
        invariant
            0 <= low && up < len,
            forall|i: int|
                (0 <= i < len && arr@[(i) as int] == value) as int != 0 ==> (low <= i <= up) as int
                    != 0,
        decreases up - low,
    {
        let mid: i32 = low + (up - low) / 2;
        if arr[mid as usize] > value {
            up = mid - 1;
        } else if arr[mid as usize] < value {
            low = mid + 1;
        } else {
            return mid;
        }
    }
    -1
}

fn main() {
}

fn valid_test_harness_bsearch() {
    // --- Test Case 1: Valid - value in middle ---
    let arr1 = [1, 2, 3, 4, 5];
    let val1 = 3;
    CheckPre_bsearch(&arr1, 5, val1);
    let result1 = 2; // Index of 3
    CheckPost_bsearch(&arr1, 5, val1, result1);

    // --- Test Case 2: Valid - first element ---
    let arr2 = [10, 20, 30];
    let val2 = 10;
    CheckPre_bsearch(&arr2, 3, val2);
    let result2 = 0;
    CheckPost_bsearch(&arr2, 3, val2, result2);

    // --- Test Case 3: Valid - last element ---
    let arr3 = [5, 6, 7, 8];
    let val3 = 8;
    CheckPre_bsearch(&arr3, 4, val3);
    let result3 = 3;
    CheckPost_bsearch(&arr3, 4, val3, result3);

    // --- Test Case 4: Valid - single element found ---
    let arr4 = [42];
    let val4 = 42;
    CheckPre_bsearch(&arr4, 1, val4);
    let result4 = 0;
    CheckPost_bsearch(&arr4, 1, val4, result4);

    // --- Test Case 5: Valid - single element not found ---
    let arr5 = [42];
    let val5 = 0;
    CheckPre_bsearch(&arr5, 1, val5);
    let result5 = -1;
    CheckPost_bsearch(&arr5, 1, val5, result5);

    // --- Test Case 6: Boundary - empty array ---
    let arr6: [i32; 0] = [];
    let val6 = 5;
    CheckPre_bsearch(&arr6, 0, val6);
    let result6 = -1;
    CheckPost_bsearch(&arr6, 0, val6, result6);

    // --- Test Case 7: Boundary - all elements same ---
    let arr7 = [2, 2, 2, 2];
    let val7 = 2;
    CheckPre_bsearch(&arr7, 4, val7);
    // Note: Any index 0-3 is technically valid for this behavior
    let result7 = 1; 
    CheckPost_bsearch(&arr7, 4, val7, result7);
}

fn invalid_test_harness_bsearch() {
    // --- Test Case 8: Invalid - negative length ---
    // Violates requires len >= 0
    let arr8 = [1, 2, 3];
    let val8 = 0;
    // Note: Rust usize is unsigned, so we simulate the C 'int' overflow/negative 
    // by passing a length that doesn't make sense for the slice.
    CheckPre_bsearch(&arr8, -1, val8);

    // --- Test Case 9: Invalid - unsorted array ---
    // Violates requires Sorted predicate
    let arr9 = [1, 3, 2, 4];
    let val9 = 2;
    CheckPre_bsearch(&arr9, 4, val9);
}

} // verus!

// RAC
// fn bsearch(arr: &[i32], len: i32, value: i32) -> i32
// {
//     if len == 0 {
//         return -1;
//     }
//     let mut low: i32 = 0;
//     let mut up: i32 = len - 1;
//     while low <= up
//     {
//         let old_measure = up - low;
//         assert!(
//             0 <= low && up < len &&
//             (0..len).all(|i| !(arr[(i) as usize] == value) || (low <= i && i <= up))
//         );
//         let mid: i32 = low + (up - low) / 2;
//         if arr[mid as usize] > value {
//             up = mid - 1;
//         } else if arr[mid as usize] < value {
//             low = mid + 1;
//         } else {
//             return mid;
//         }
//         assert!(old_measure > up - low);
//     }
//     assert!(
//         0 <= low && up < len &&
//         (0..len).all(|i| !(arr[(i) as usize] == value) || (low <= i && i <= up))
//     );
//     -1
// }

// fn main() {
//     valid_test_harness_bsearch();
// }

// fn valid_test_harness_bsearch() {
//     // --- Test Case 1: Valid - value in middle ---
//     let arr1 = [1, 2, 3, 4, 5];
//     let val1 = 3;
//     bsearch(&arr1, 5, val1);

//     // --- Test Case 2: Valid - first element ---
//     let arr2 = [10, 20, 30];
//     let val2 = 10;
//     bsearch(&arr2, 3, val2);

//     // --- Test Case 3: Valid - last element ---
//     let arr3 = [5, 6, 7, 8];
//     let val3 = 8;
//     bsearch(&arr3, 4, val3);

//     // --- Test Case 4: Valid - single element found ---
//     let arr4 = [42];
//     let val4 = 42;
//     bsearch(&arr4, 1, val4);

//     // --- Test Case 5: Valid - single element not found ---
//     let arr5 = [42];
//     let val5 = 0;
//     bsearch(&arr5, 1, val5);

//     // --- Test Case 6: Boundary - empty array ---
//     let arr6: [i32; 0] = [];
//     let val6 = 5;
//     bsearch(&arr6, 0, val6);

//     // --- Test Case 7: Boundary - all elements same ---
//     let arr7 = [2, 2, 2, 2];
//     let val7 = 2;
//     bsearch(&arr7, 4, val7);
// }