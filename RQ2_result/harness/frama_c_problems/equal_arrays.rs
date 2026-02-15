#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn check(a: &[i32], b: &[i32], n: i32) -> (result: i32)
    requires
        n > 0,
        a@.len() >= n - 1 + 1,
        b@.len() >= n - 1 + 1,
    ensures
        (forall|k: int| (0 <= k < n) as int != 0 ==> (b@[(k) as int] == a@[(k) as int]) as int != 0)
            ==> (result == 1),
        (exists|k: int| 0 <= k < n && b@[(k) as int] != a@[(k) as int]) ==> (result == 0),
{
    let mut i: i32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int|
                (0 <= k < i) as int != 0 ==> (a@[(k) as int] == b@[(k) as int]) as int != 0,
        decreases n - i,
    {
        if a[i as usize] != b[i as usize] {
            return 0;
        }
        i += 1;
    }
    return 1;
}

fn CheckPre_check(a: &[i32], b: &[i32], n: i32)
    requires
        n > 0,
        a@.len() >= n - 1 + 1,
        b@.len() >= n - 1 + 1,
{}

fn CheckPost_check(a: &[i32], b: &[i32], n: i32, result: i32)
    requires
        (forall|k: int| (0 <= k < n) as int != 0 ==> (b@[(k) as int] == a@[(k) as int]) as int != 0)
            ==> (result == 1),
        (exists|k: int| 0 <= k < n && b@[(k) as int] != a@[(k) as int]) ==> (result == 0),
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let a: [i32; 5] = [1, 2, 3, 4, 5];
    let b: [i32; 5] = [1, 2, 3, 4, 5];
    check(&a, &b, 5);
}

fn valid_test_harness_check() {
    // Test case 1: Valid - equal arrays with n=5
    let a1 = [1, 2, 3, 4, 5];
    let b1 = [1, 2, 3, 4, 5];
    CheckPre_check(&a1, &b1, 5);
    let result1 = 1;
    CheckPost_check(&a1, &b1, 5, result1);

    // Test case 2: Valid - arrays differ at index 1 with n=3
    let a2 = [1, 2, 3];
    let b2 = [1, 9, 3];
    CheckPre_check(&a2, &b2, 3);
    let result2 = 0;
    CheckPost_check(&a2, &b2, 3, result2);

    // Test case 3: Valid - arrays differ at last element with n=3
    let a3 = [10, 20, 30];
    let b3 = [10, 20, 40];
    CheckPre_check(&a3, &b3, 3);
    let result3 = 0;
    CheckPost_check(&a3, &b3, 3, result3);

    // Test case 4: Valid - equal arrays with n=1
    let a4 = [42];
    let b4 = [42];
    CheckPre_check(&a4, &b4, 1);
    let result4 = 1;
    CheckPost_check(&a4, &b4, 1, result4);

    // Test case 5: Valid - arrays differ at index 2 with n=4
    let a5 = [5, 5, 5, 5];
    let b5 = [5, 5, 6, 5];
    CheckPre_check(&a5, &b5, 4);
    let result5 = 0;
    CheckPost_check(&a5, &b5, 4, result5);

    // Test case 6: Boundary - minimum valid n=1 with equal elements
    let a6 = [100];
    let b6 = [100];
    CheckPre_check(&a6, &b6, 1);
    let result6 = 1;
    CheckPost_check(&a6, &b6, 1, result6);

    // Test case 7: Boundary - minimum valid n=1 with different elements
    let a7 = [50];
    let b7 = [60];
    CheckPre_check(&a7, &b7, 1);
    let result7 = 0;
    CheckPost_check(&a7, &b7, 1, result7);
}

fn invalid_test_harness_check() {
    // Test case 8: Invalid - n=0 violates n > 0
    let a8 = [0];
    let b8 = [0];
    CheckPre_check(&a8, &b8, 0);

    // Test case 9: Invalid - a=NULL equivalent
    let b9 = [1, 2, 3];
    CheckPre_check(&[], &b9, 3);
}

} // verus!

// RAC
// fn check(a: &[i32], b: &[i32], n: i32) -> i32
// {
//     let mut i: i32 = 0;
//     while i < n
//     {
//         let old_measure = n - i;
//         assert!(
//             0 <= i && i <= n &&
//             (0..i).all(|k| a[(k) as usize] == b[(k) as usize])
//         );
//         if a[i as usize] != b[i as usize] {
//             return 0;
//         }
//         i += 1;
//         assert!(old_measure > n - i);
//     }
//     assert!(
//         0 <= i && i <= n &&
//         (0..i).all(|k| a[(k) as usize] == b[(k) as usize])
//     );
//     return 1;
// }

// fn valid_test_harness_check() {
//     // Test case 1: Valid - equal arrays with n=5
//     let a1 = [1, 2, 3, 4, 5];
//     let b1 = [1, 2, 3, 4, 5];
//     check(&a1, &b1, 5);

//     // Test case 2: Valid - arrays differ at index 1 with n=3
//     let a2 = [1, 2, 3];
//     let b2 = [1, 9, 3];
//     check(&a2, &b2, 3);

//     // Test case 3: Valid - arrays differ at last element with n=3
//     let a3 = [10, 20, 30];
//     let b3 = [10, 20, 40];
//     check(&a3, &b3, 3);

//     // Test case 4: Valid - equal arrays with n=1
//     let a4 = [42];
//     let b4 = [42];
//     check(&a4, &b4, 1);

//     // Test case 5: Valid - arrays differ at index 2 with n=4
//     let a5 = [5, 5, 5, 5];
//     let b5 = [5, 5, 6, 5];
//     check(&a5, &b5, 4);

//     // Test case 6: Boundary - minimum valid n=1 with equal elements
//     let a6 = [100];
//     let b6 = [100];
//     check(&a6, &b6, 1);

//     // Test case 7: Boundary - minimum valid n=1 with different elements
//     let a7 = [50];
//     let b7 = [60];
//     check(&a7, &b7, 1);
// }

// fn main(){
//     valid_test_harness_check();
// }