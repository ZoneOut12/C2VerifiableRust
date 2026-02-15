#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

fn CheckPre_copy(original: &[i32], old_copy: &[i32], length: i32)
    requires
        0 <= length,
        original@.len() >= length - 1 + 1,
        old_copy@.len() >= length - 1 + 1,
{}

fn CheckPost_copy(original: &[i32], copy: &[i32], length: i32)
    requires
        forall|j: int|
            (0 <= j < length) as int != 0 ==> (original@[(j) as int] == copy@[(j) as int]) as int
                != 0,
{}

#[verifier::external_body]
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn copy(original: &[i32], copy: &mut [i32], length: i32)
    requires
        0 <= length,
        original@.len() >= length - 1 + 1,
        old(copy)@.len() >= length - 1 + 1,
        true,
    ensures
        forall|j: int|
            (0 <= j < length) as int != 0 ==> (original@[(j) as int] == copy@[(j) as int]) as int
                != 0,
{
    let mut i: i32 = 0;
    while i < length
        invariant
            0 <= i <= length,
            forall|j: int|
                (0 <= j < i) as int != 0 ==> (original@[(j) as int] == copy@[(j) as int]) as int
                    != 0,
        decreases length - i,
    {
        copy[i as usize] = original[i as usize];
        i += 1;
    }
}

fn CheckPre_foo(old_a: &[i32])
    requires
        old_a@.len() >= 9 + 1,
{}

fn CheckPost_foo(old_a: &[i32], a: &[i32])
    requires
        forall|j: int|
            (0 <= j < 10) as int != 0 ==> (a@[(j) as int] == old_a@[(j) as int]) as int != 0
{}

#[verifier::external_body]
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(a: &mut [i32])
    requires
        old(a)@.len() >= 9 + 1,
    ensures
        forall|j: int|
            (0 <= j < 10) as int != 0 ==> (a@[(j) as int] == old(a)@[(j) as int]) as int != 0,
{
    let mut g: [i32; 10] = [0;10];
    copy(a, &mut g, 10);

    let mut i: i32 = 0;
    while i < 10
        invariant
            0 <= i <= 10,
            forall|j: int|
                (0 <= j < 10) as int != 0 ==> (a@[(j) as int] == g@[(j) as int]) as int != 0,
        decreases 10 - i,
    {
        i += 1;
    }
}

fn main() {
}

fn valid_test_harness_copy() {
    // --- Test Case 1: Standard copy (positive numbers) ---
    let original1 = [1, 2, 3, 4];
    let mut actual_copy1 = [0; 4];
    let expected_copy1 = [1, 2, 3, 4];
    CheckPre_copy(&original1, &actual_copy1, 4);
    // After calling copy()...
    CheckPost_copy(&original1, &expected_copy1, 4);

    // --- Test Case 2: Copying mixed values ---
    let original2 = [10, -5, 0, 99];
    let mut actual_copy2 = [0; 4];
    let expected_copy2 = [10, -5, 0, 99];
    CheckPre_copy(&original2, &actual_copy2, 4);
    CheckPost_copy(&original2, &expected_copy2, 4);

    // --- Test Case 3: Boundary - length 0 (empty copy) ---
    let original3: [i32; 0] = [];
    let mut actual_copy3: [i32; 0] = [];
    let expected_copy3: [i32; 0] = [];
    CheckPre_copy(&original3, &actual_copy3, 0);
    CheckPost_copy(&original3, &expected_copy3, 0);

    // --- Test Case 4: Boundary - length 1 (single element) ---
    let original4 = [42];
    let mut actual_copy4 = [0];
    let expected_copy4 = [42];
    CheckPre_copy(&original4, &actual_copy4, 1);
    CheckPost_copy(&original4, &expected_copy4, 1);

    // --- Test Case 5: Original contains zeros ---
    let original5 = [0, 0, 0];
    let mut actual_copy5 = [1, 2, 3];
    let expected_copy5 = [0, 0, 0];
    CheckPre_copy(&original5, &actual_copy5, 3);
    CheckPost_copy(&original5, &expected_copy5, 3);

    // --- Test Case 6: Large length ---
    let original6 = [7; 100];
    let mut actual_copy6 = [0; 100];
    let expected_copy6 = [7; 100];
    CheckPre_copy(&original6, &actual_copy6, 100);
    CheckPost_copy(&original6, &expected_copy6, 100);

    // --- Test Case 7: Different buffer sizes ---
    let original7 = [1, 2];
    let mut actual_copy7 = [0, 0, 0, 0, 0];
    let expected_copy7 = [1, 2]; // We only check the first 'length' elements
    CheckPre_copy(&original7, &actual_copy7, 2);
    CheckPost_copy(&original7, &expected_copy7, 2);
}


fn invalid_test_harness_copy() {
    // --- Test Case 8: Invalid - length exceeds buffer size ---
    // Violates \valid(copy+(0 .. length-1))
    let original8 = [1, 2, 3];
    let mut copy8 = [0, 0];
    // CheckPre_copy(&original8, &copy8, 3);
}


fn valid_test_harness_foo() {
    // --- Test Case 1: Valid - sequential numbers ---
    let old_a1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let a1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]; // Simulated state after foo()
    CheckPre_foo(&a1);
    CheckPost_foo(&old_a1, &a1);

    // --- Test Case 2: Valid - all elements same ---
    let old_a2 = [5; 10];
    let a2 = [5; 10];
    CheckPre_foo(&a2);
    CheckPost_foo(&old_a2, &a2);

    // --- Test Case 3: Valid - mixed positive/negative ---
    let old_a3 = [-1, 2, -3, 4, -5, 6, -7, 8, -9, 10];
    let a3 = [-1, 2, -3, 4, -5, 6, -7, 8, -9, 10];
    CheckPre_foo(&a3);
    CheckPost_foo(&old_a3, &a3);

    // --- Test Case 4: Valid - descending order ---
    let old_a4 = [10, 9, 8, 7, 6, 5, 4, 3, 2, 1];
    let a4 = [10, 9, 8, 7, 6, 5, 4, 3, 2, 1];
    CheckPre_foo(&a4);
    CheckPost_foo(&old_a4, &a4);

    // --- Test Case 5: Valid - first element non-zero ---
    let old_a5 = [42, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let a5 = [42, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    CheckPre_foo(&a5);
    CheckPost_foo(&old_a5, &a5);

    // --- Test Case 6: Boundary - all zeros ---
    let old_a6 = [0; 10];
    let a6 = [0; 10];
    CheckPre_foo(&a6);
    CheckPost_foo(&old_a6, &a6);

    // --- Test Case 7: Boundary - array size exactly 10 ---
    let old_a7 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let a7 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    CheckPre_foo(&a7);
    CheckPost_foo(&old_a7, &a7);
}

fn invalid_test_harness_foo() {
    // --- Test Case 8: Invalid - NULL array ---
    // Violates \valid(a + (0..9))
    let a8 = [0];
    CheckPre_foo(&a8);

    // --- Test Case 9: Invalid - array size 9 ---
    // Violates the requirement for a valid range of 10 elements
    let a9 = [1, 2, 3, 4, 5, 6, 7, 8, 9];
    CheckPre_foo(&a9); 
}

} // verus!


// RAC

// fn copy(original: &[i32], copy: &mut [i32], length: i32)
// {
//     let mut i: i32 = 0;
//     while i < length
//     {
//         let old_measure = length - i;
//         assert!(
//             0 <= i && i <= length &&
//             (0..i).all(|j| original[(j) as usize] == copy[(j) as usize])
//         );
//         copy[i as usize] = original[i as usize];
//         i += 1;
//         assert!(old_measure > length - i);
//     }
//     assert!(
//         0 <= i && i <= length &&
//         (0..i).all(|j| original[(j) as usize] == copy[(j) as usize])
//     );
// }

// fn foo(a: &mut [i32])
// {
//     let mut g: [i32; 10] = [0;10];
//     copy(a, &mut g, 10);

//     let mut i: i32 = 0;
//     while i < 10
//     {
//         let old_measure = 10 - i; 
//         assert!(
//             0 <= i && i <= 10 &&
//             (0..10).all(|j| a[(j) as usize] == g[(j) as usize])
//         );
//         i += 1;
//         assert!(old_measure > 10 - i);
//     }
//     assert!(
//         0 <= i && i <= 10 &&
//         (0..10).all(|j| a[(j) as usize] == g[(j) as usize])
//     );
// }

// fn main() {
//     valid_test_harness_copy();
//     invalid_test_harness_copy();
//     valid_test_harness_foo();
// }

// fn valid_test_harness_copy() {
//     // --- Test Case 1: Standard copy (positive numbers) ---
//     let original1 = [1, 2, 3, 4];
//     let mut actual_copy1 = [0; 4];
//     let expected_copy1 = [1, 2, 3, 4];
//     copy(&original1, &mut actual_copy1, 4);

//     // --- Test Case 2: Copying mixed values ---
//     let original2 = [10, -5, 0, 99];
//     let mut actual_copy2 = [0; 4];
//     let expected_copy2 = [10, -5, 0, 99];
//     copy(&original2, &mut actual_copy2, 4);

//     // --- Test Case 3: Boundary - length 0 (empty copy) ---
//     let original3: [i32; 0] = [];
//     let mut actual_copy3: [i32; 0] = [];
//     let expected_copy3: [i32; 0] = [];
//     copy(&original3, &mut actual_copy3, 0);

//     // --- Test Case 4: Boundary - length 1 (single element) ---
//     let original4 = [42];
//     let mut actual_copy4 = [0];
//     let expected_copy4 = [42];
//     copy(&original4, &mut actual_copy4, 1);

//     // --- Test Case 5: Original contains zeros ---
//     let original5 = [0, 0, 0];
//     let mut actual_copy5 = [1, 2, 3];
//     let expected_copy5 = [0, 0, 0];
//     copy(&original5, &mut actual_copy5, 3);

//     // --- Test Case 6: Large length ---
//     let original6 = [7; 100];
//     let mut actual_copy6 = [0; 100];
//     let expected_copy6 = [7; 100];
//     copy(&original6, &mut actual_copy6, 100);

//     // --- Test Case 7: Different buffer sizes ---
//     let original7 = [1, 2];
//     let mut actual_copy7 = [0, 0, 0, 0, 0];
//     let expected_copy7 = [1, 2]; // We only check the first 'length' elements
//     copy(&original7, &mut actual_copy7, 2);
// }

// fn valid_test_harness_foo() {
//     // --- Test Case 1: Valid - sequential numbers ---
//     let mut a1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]; // Simulated state after foo()
//     foo(&mut a1);

//     // --- Test Case 2: Valid - all elements same ---
//     let mut a2 = [5; 10];
//     foo(&mut a2);

//     // --- Test Case 3: Valid - mixed positive/negative ---
//     let mut a3 = [-1, 2, -3, 4, -5, 6, -7, 8, -9, 10];
//     foo(&mut a3);

//     // --- Test Case 4: Valid - descending order ---
//     let mut a4 = [10, 9, 8, 7, 6, 5, 4, 3, 2, 1];
//     foo(&mut a4);

//     // --- Test Case 5: Valid - first element non-zero ---
//     let mut a5 = [42, 0, 0, 0, 0, 0, 0, 0, 0, 0];
//     foo(&mut a5);

//     // --- Test Case 6: Boundary - all zeros ---
//     let mut a6 = [0; 10];
//     foo(&mut a6);

//     // --- Test Case 7: Boundary - array size exactly 10 ---
//     let mut a7 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
//     foo(&mut a7);
// }

// fn invalid_test_harness_copy() {
//     // --- Test Case 9: Invalid - Not separated (Aliasing) ---
//     let mut arr9 = [1, 2, 3];
//     copy(&arr9, &mut arr9, 3);
// }