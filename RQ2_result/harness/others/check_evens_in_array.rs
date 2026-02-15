#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

fn CheckPre_areElementsEven(a: &[i32], n: i32)
    requires
        n > 0,
        a@.len() >= (n - 1) + 1,
{}

fn CheckPost_areElementsEven(a: &[i32], n: i32, result: i32)
    requires
        (forall|k: int| (0 <= k < n) as int != 0 ==> (a@[(k) as int] % 2 == 0) as int != 0) ==> (
        result == 1),
        (exists|k: int| 0 <= k < n && a@[(k) as int] % 2 != 0) ==> (result == 0),
{}

#[verifier::external_body]
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn areElementsEven(a: &[i32], n: i32) -> (result: i32)
    requires
        n > 0,
        a@.len() >= (n - 1) + 1,
    ensures
        (forall|k: int| (0 <= k < n) as int != 0 ==> (a@[(k) as int] % 2 == 0) as int != 0) ==> (
        result == 1),
        (exists|k: int| 0 <= k < n && a@[(k) as int] % 2 != 0) ==> (result == 0),
{
    let mut p: i32 = 0;
    while p < n
        invariant
            0 <= p <= n,
            forall|k: int| (0 <= k < p) as int != 0 ==> (a@[(k) as int] % 2 == 0) as int != 0,
        decreases n - p,
    {
        if a[p as usize] % 2 != 0 {
            return 0;
        }
        p += 1;
    }
    return 1;
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let arr: [i32; 5] = [2, 4, 6, 8, 10];
    let res: i32 = areElementsEven(&arr, 5);
    assert(res == 1);
}

fn valid_test_harness_are_elements_even() {
    // --- Test Case 1: Valid - all even elements ---
    let arr1 = [2, 4, 6, 8, 10];
    CheckPre_areElementsEven(&arr1, 5);
    let result1 = 1; 
    CheckPost_areElementsEven(&arr1, 5, result1);

    // --- Test Case 2: Valid - contains odd element ---
    let arr2 = [2, 3, 4];
    CheckPre_areElementsEven(&arr2, 3);
    let result2 = 0; 
    CheckPost_areElementsEven(&arr2, 3, result2);

    // --- Test Case 3: Valid - single even element ---
    let arr3 = [4];
    CheckPre_areElementsEven(&arr3, 1);
    let result3 = 1;
    CheckPost_areElementsEven(&arr3, 1, result3);

    // --- Test Case 4: Valid - single odd element ---
    let arr4 = [5];
    CheckPre_areElementsEven(&arr4, 1);
    let result4 = 0;
    CheckPost_areElementsEven(&arr4, 1, result4);

    // --- Test Case 5: Valid - all zeros ---
    let arr5 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    CheckPre_areElementsEven(&arr5, 10);
    let result5 = 1;
    CheckPost_areElementsEven(&arr5, 10, result5);

    // --- Test Case 8: Boundary - minimum valid n with even ---
    let arr8 = [2];
    CheckPre_areElementsEven(&arr8, 1);
    let result8 = 1;
    CheckPost_areElementsEven(&arr8, 1, result8);

    // --- Test Case 9: Boundary - minimum valid n with odd ---
    let arr9 = [3];
    CheckPre_areElementsEven(&arr9, 1);
    let result9 = 0;
    CheckPost_areElementsEven(&arr9, 1, result9);
}

fn invalid_test_harness_are_elements_even() {
    // --- Test Case 6: Invalid - n = 0 (Violates n > 0) ---
    let arr6 = [0];
    CheckPre_areElementsEven(&arr6, 0);

    // --- Test Case 7: Invalid - NULL array pointer (Violates \valid_read) ---
    // let ptr7: *const i32 = std::ptr::null();
    // CheckPre_areElementsEven(ptr7, 3);
}

} // verus!


// RAC
// fn areElementsEven(a: &[i32], n: i32) -> i32
// {
//     let mut p: i32 = 0;
//     while p < n
//     {
//         let old_measure = n - p;
//         assert!(
//             0 <= p && p <= n &&
//             (0..p).all(|k| a[(k) as usize] % 2 == 0)
//         );
//         if a[p as usize] % 2 != 0 {
//             return 0;
//         }
//         p += 1;
//         assert!(old_measure > n- p);
//     }
//     assert!(
//         0 <= p && p <= n &&
//         (0..p).all(|k| a[(k) as usize] % 2 == 0)
//     );
//     return 1;
// }

// fn main() {
//     valid_test_harness_are_elements_even();

//     let arr: [i32; 5] = [2, 4, 6, 8, 10];
//     let res: i32 = areElementsEven(&arr, 5);
//     assert!(res == 1);
// }

// fn valid_test_harness_are_elements_even() {
//     // --- Test Case 1: Valid - all even elements ---
//     let arr1 = [2, 4, 6, 8, 10];
//     areElementsEven(&arr1, 5);

//     // --- Test Case 2: Valid - contains odd element ---
//     let arr2 = [2, 3, 4];
//     areElementsEven(&arr2, 3);

//     // --- Test Case 3: Valid - single even element ---
//     let arr3 = [4];
//     areElementsEven(&arr3, 1);

//     // --- Test Case 4: Valid - single odd element ---
//     let arr4 = [5];
//     areElementsEven(&arr4, 1);

//     // --- Test Case 5: Valid - all zeros ---
//     let arr5 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
//     areElementsEven(&arr5, 10);

//     // --- Test Case 8: Boundary - minimum valid n with even ---
//     let arr8 = [2];
//     areElementsEven(&arr8, 1);

//     // --- Test Case 9: Boundary - minimum valid n with odd ---
//     let arr9 = [3];
//     areElementsEven(&arr9, 1);
// }