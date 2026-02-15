// #[allow(unused_imports)]
// use vstd::math::*;
// use vstd::prelude::*;
// use vstd::slice::*;
// verus! {

// #[verifier::loop_isolation(false)]
// #[verifier::exec_allows_no_decreases_clause]
// fn array_find(arr: &[i32], n: i32, x: i32) -> (result: i32)
//     requires
//         n >= 0,
//         arr@.len() >= n - 1 + 1,
//     ensures
//         -1 <= result < n,
//         (0 <= result < n) as int != 0 ==> (arr@[(result) as int] == x) as int != 0,
//         ((result == -1)) as int != 0 ==> ((forall|i: int|
//             (0 <= i < n) as int != 0 ==> (arr@[(i) as int] != x) as int != 0)) as int != 0,
// {
//     let mut i: i32 = 0;
//     while i < n
//         invariant
//             0 <= i <= n,
//             forall|k: int| (0 <= k < i) as int != 0 ==> (arr@[(k) as int] != x) as int != 0,
//         decreases n - i,
//     {
//         if arr[i as usize] == x {
//             return i;
//         }
//         i += 1;
//     }
//     -1
// }

// fn CheckPre_array_find(arr: &[i32], n: i32, x: i32)
//     requires
//         n >= 0,
//         arr@.len() >= n - 1 + 1,
// {}

// fn CheckPost_array_find(arr: &[i32], n: i32, x: i32, result: i32)
//     requires
//         -1 <= result < n,
//         (0 <= result < n) as int != 0 ==> (arr@[(result) as int] == x) as int != 0,
//         ((result == -1)) as int != 0 ==> ((forall|i: int|
//             (0 <= i < n) as int != 0 ==> (arr@[(i) as int] != x) as int != 0)) as int != 0,
// {}

// fn main() {
// }

// fn valid_test_harness_array_find() {
//     // Test case 1: Valid - x found in the middle
//     let arr1 = [10, 20, 30, 40];
//     CheckPre_array_find(&arr1, 4, 30);
//     let result1 = 2;
//     CheckPost_array_find(&arr1, 4, 30, result1);

//     // Test case 2: Valid - x is the first element
//     let arr2 = [5, 15, 25];
//     CheckPre_array_find(&arr2, 3, 5);
//     let result2 = 0;
//     CheckPost_array_find(&arr2, 3, 5, result2);

//     // Test case 3: Valid - x is the last element
//     let arr3 = [1, 3, 5];
//     CheckPre_array_find(&arr3, 3, 5);
//     let result3 = 2;
//     CheckPost_array_find(&arr3, 3, 5, result3);

//     // Test case 4: Valid - x not found
//     let arr4 = [2, 4, 6, 8];
//     CheckPre_array_find(&arr4, 4, 5);
//     let result4 = -1;
//     CheckPost_array_find(&arr4, 4, 5, result4);

//     // Test case 5: Valid - single-element array with x found
//     let arr5 = [42];
//     CheckPre_array_find(&arr5, 1, 42);
//     let result5 = 0;
//     CheckPost_array_find(&arr5, 1, 42, result5);

//     // Test case 6: Boundary - empty array (n=0)
//     let arr6: [i32; 0] = [];
//     CheckPre_array_find(&arr6, 0, 99);
//     let result6 = -1;
//     CheckPost_array_find(&arr6, 0, 99, result6);

//     // Test case 7: Boundary - single-element array with x not found
//     let arr7 = [77];
//     CheckPre_array_find(&arr7, 1, 0);
//     let result7 = -1;
//     CheckPost_array_find(&arr7, 1, 0, result7);
// }

// fn invalid_test_harness_array_find() {
//     // Test case 8: Invalid - negative n
//     // Note: Rust's usize/isize prevents negative indexing, 
//     // but we simulate the check with an i32 parameter.
//     let arr8 = [1, 2, 3];
//     CheckPre_array_find(&arr8, -3, 0);

//     // Test case 9: Invalid - NULL array pointer
//     // In Rust, using Option::None or raw pointers represents NULL.
//     // Using references (&) guarantees validity at compile time.
//     let arr9 = [];
//     CheckPre_array_find(&arr9, 2, 5);
// }

// } // verus!


// RAC
fn array_find(arr: &[i32], n: i32, x: i32) -> i32
{
    let mut i: i32 = 0;
    while i < n
    {
        let old_measure = n - i;
        assert!(
            0 <= i && i <= n &&
            (0..i).all(|k| arr[(k) as usize] != x)
        );
        if arr[i as usize] == x {
            return i;
        }
        i += 1;
        assert!(old_measure > n - i);
    }
    assert!(
        0 <= i && i <= n &&
        (0..i).all(|k| arr[(k) as usize] != x)
    );
    -1
}

fn main() {
    valid_test_harness_array_find();
}

fn valid_test_harness_array_find() {
    // Test case 1: Valid - x found in the middle
    let arr1 = [10, 20, 30, 40];
    array_find(&arr1, 4, 30);

    // Test case 2: Valid - x is the first element
    let arr2 = [5, 15, 25];
    array_find(&arr2, 3, 5);

    // Test case 3: Valid - x is the last element
    let arr3 = [1, 3, 5];
    array_find(&arr3, 3, 5);

    // Test case 4: Valid - x not found
    let arr4 = [2, 4, 6, 8];
    array_find(&arr4, 4, 5);

    // Test case 5: Valid - single-element array with x found
    let arr5 = [42];
    array_find(&arr5, 1, 42);

    // Test case 6: Boundary - empty array (n=0)
    let arr6: [i32; 0] = [];
    array_find(&arr6, 0, 99);

    // Test case 7: Boundary - single-element array with x not found
    let arr7 = [77];
    array_find(&arr7, 1, 0);
}