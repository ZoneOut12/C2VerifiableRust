#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn member(p: &[i32], n: i32, v: i32) -> (result: i32)
    requires
        n > 0 && p@.len() >= n - 1 + 1,
    ensures
        (result == -1) as int != 0 ==> (!(((exists|i: i32|
            0 <= i < n && p@[(i) as int] == v)) as int != 0)) as int != 0,
        (result != -1) as int != 0 ==> (0 <= result < n && p@[(result) as int] == v) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            (0 <= i <= n),
            !(((exists|j: i32| 0 <= j < i && p@[(j) as int] == v)) as int != 0),
        decreases n - i,
    {
        if p[i as usize] == v {
            return i;
        }
        i += 1;
    }
    -1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn member_noreturn(p: &[i32], n: i32, v: i32) -> (result: i32)
    requires
        n > 0 && p@.len() >= n - 1 + 1,
    ensures
        (result == -1) as int != 0 ==> (!(((exists|i: i32|
            0 <= i < n && p@[(i) as int] == v)) as int != 0)) as int != 0,
        (result != -1) as int != 0 ==> (0 <= result < n && p@[(result) as int] == v) as int != 0,
{
    let mut r: i32 = -1;
    let mut i: i32 = 0;
    while i < n
        invariant
            (0 <= i <= n),
            (r == -1) as int != 0 ==> (!(((exists|j: i32| 0 <= j < i && p@[(j) as int] == v)) as int
                != 0)) as int != 0,
            (r != -1) as int != 0 ==> (0 <= r < n && p@[(r) as int] == v) as int != 0,
        decreases n - i,
    {
        if r == -1 && p[i as usize] == v {
            r = i;
        }
        i += 1;
    }
    r
}

fn CheckPre_member(p: &[i32], n: i32, v: i32)
    requires
        n > 0 && p@.len() >= n - 1 + 1,
{}

fn CheckPost_member(p: &[i32], n: i32, v: i32, result:i32)
    requires
        (result == -1) as int != 0 ==> (!(((exists|i: i32|
            0 <= i < n && p@[(i) as int] == v)) as int != 0)) as int != 0,
        (result != -1) as int != 0 ==> (0 <= result < n && p@[(result) as int] == v) as int != 0,
{}


fn CheckPre_member_noreturn(p: &[i32], n: i32, v: i32)
    requires
        n > 0 && p@.len() >= n - 1 + 1,
{}

fn CheckPost_member_noreturn(p: &[i32], n: i32, v: i32, result:i32)
    requires
        (result == -1) as int != 0 ==> (!(((exists|i: i32|
            0 <= i < n && p@[(i) as int] == v)) as int != 0)) as int != 0,
        (result != -1) as int != 0 ==> (0 <= result < n && p@[(result) as int] == v) as int != 0,
{}

fn main() {
}

fn valid_test_harness() {
    // Test case 1: Element at first position [5, 2, 3]
    let arr1 = [5, 2, 3];
    CheckPre_member(&arr1, 3, 5);
    let result1 = 0; // Hardcoded output
    CheckPost_member(&arr1, 3, 5, result1);
    
    CheckPre_member_noreturn(&arr1, 3, 5);
    let result1_noreturn = 0; 
    CheckPost_member_noreturn(&arr1, 3, 5, result1_noreturn);

    // Test case 2: Element in middle [1, 3, 5, 7, 9]
    let arr2 = [1, 3, 5, 7, 9];
    CheckPre_member(&arr2, 5, 5);
    let result2 = 2;
    CheckPost_member(&arr2, 5, 5, result2);
    
    CheckPre_member_noreturn(&arr2, 5, 5);
    let result2_noreturn = 2;
    CheckPost_member_noreturn(&arr2, 5, 5, result2_noreturn);

    // Test case 3: Element not found [10, 20, 30, 40]
    let arr3 = [10, 20, 30, 40];
    CheckPre_member(&arr3, 4, 15);
    let result3 = -1;
    CheckPost_member(&arr3, 4, 15, result3);
    
    CheckPre_member_noreturn(&arr3, 4, 15);
    let result3_noreturn = -1;
    CheckPost_member_noreturn(&arr3, 4, 15, result3_noreturn);

    // Test case 4: Element at last position [10, 20, 30, 40]
    let arr4 = [10, 20, 30, 40];
    CheckPre_member(&arr4, 4, 40);
    let result4 = 3;
    CheckPost_member(&arr4, 4, 40, result4);
    
    CheckPre_member_noreturn(&arr4, 4, 40);
    let result4_noreturn = 3;
    CheckPost_member_noreturn(&arr4, 4, 40, result4_noreturn);

    // Test case 5: Multiple occurrences [2, 2, 2, 2, 2]
    let arr5 = [2, 2, 2, 2, 2];
    CheckPre_member(&arr5, 5, 2);
    let result5 = 0;
    CheckPost_member(&arr5, 5, 2, result5);
    
    CheckPre_member_noreturn(&arr5, 5, 2);
    let result5_noreturn = 0;
    CheckPost_member_noreturn(&arr5, 5, 2, result5_noreturn);

    // Test case 8: Boundary - n=1 with element present [42]
    let arr8 = [42];
    CheckPre_member(&arr8, 1, 42);
    let result8 = 0;
    CheckPost_member(&arr8, 1, 42, result8);
    
    CheckPre_member_noreturn(&arr8, 1, 42);
    let result8_noreturn = 0;
    CheckPost_member_noreturn(&arr8, 1, 42, result8_noreturn);

    // Test case 9: Boundary - n=1 with element not present [42]
    let arr9 = [42];
    CheckPre_member(&arr9, 1, 0);
    let result9 = -1;
    CheckPost_member(&arr9, 1, 0, result9);
    
    CheckPre_member_noreturn(&arr9, 1, 0);
    let result9_noreturn = -1;
    CheckPost_member_noreturn(&arr9, 1, 0, result9_noreturn);
}

fn invalid_test_harness() {
    // Test case 6
    let arr6 = [1, 2, 3];
    CheckPre_member(&arr6, 0, 5);
    CheckPre_member_noreturn(&arr6, 0, 5);

    // Test case 7
    let arr7: [i32; 0] = [];
    CheckPre_member(&arr7, 3, 5);
    CheckPre_member_noreturn(&arr7, 3, 5);
}

} // verus!

// RAC
// fn member(p: &[i32], n: i32, v: i32) -> i32
// {
//     let mut i: i32 = 0;
//     while i < n
//     {
//         let old_measure = n - i;
//         assert!(
//             (0 <= i && i <= n) &&
//             !(0..i).any(|j| p[(j) as usize] == v)
//         );
//         if p[i as usize] == v {
//             return i;
//         }
//         i += 1;
//         assert!(old_measure > n - i);
//     }
//     assert!(
//         (0 <= i && i <= n) &&
//         !(0..i).any(|j| p[(j) as usize] == v)
//     );
//     -1
// }

// fn member_noreturn(p: &[i32], n: i32, v: i32) -> i32
// {
//     let mut r: i32 = -1;
//     let mut i: i32 = 0;
//     while i < n
//     {
//         let old_measure = n - i;
//         assert!(
//             (0 <= i && i <= n) &&
//             (!(r == -1) || (!(0..i).any(|j| p[j as usize] == v))) &&
//             (!(r != -1) || (0 <= r && r < n && p[r as usize] == v))
//         );
//         if r == -1 && p[i as usize] == v {
//             r = i;
//         }
//         i += 1;
//         assert!(old_measure > n - i);
//     }
//     assert!(
//         (0 <= i && i <= n) &&
//         (!(r == -1) || (!(0..i).any(|j| p[j as usize] == v))) &&
//         (!(r != -1) || (0 <= r && r < n && p[r as usize] == v))
//     );
//     r
// }

// fn main() {
//     valid_test_harness();
// }

// fn valid_test_harness() {
//     // Test case 1: Element at first position [5, 2, 3]
//     let arr = [5, 2, 3];
//     member(&arr, 3, 5);
//     member_noreturn(&arr, 3, 5);

//     // Test case 2: Element in middle [1, 3, 5, 7, 9]
//     let arr = [1, 3, 5, 7, 9];
//     member(&arr, 5, 5);
//     member_noreturn(&arr, 5, 5);
    
//     // Test case 3: Element not found [10, 20, 30, 40]
//     let arr = [10, 20, 30, 40];
//     member(&arr, 4, 15);
//     member_noreturn(&arr, 4, 15);

//     // Test case 4: Element at last position [10, 20, 30, 40]
//     let arr = [10, 20, 30, 40];
//     member(&arr, 4, 40);
//     member_noreturn(&arr, 4, 40);

//     // Test case 5: Multiple occurrences [2, 2, 2, 2, 2]
//     let arr = [2, 2, 2, 2, 2];
//     member(&arr, 5, 2);
//     member_noreturn(&arr, 5, 2);

//     // Test case 8: Boundary - n=1 with element present [42]
//     let arr = [42];
//     member(&arr, 1, 42);
//     member_noreturn(&arr, 1, 42);

//     // Test case 9: Boundary - n=1 with element not present [42]
//     let arr = [42];
//     member(&arr, 1, 0);
//     member_noreturn(&arr, 1, 0);
// }