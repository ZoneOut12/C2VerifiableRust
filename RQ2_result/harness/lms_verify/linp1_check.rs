#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn inv_matrix_Boolean(x26: &[i32], x27: int, x28: int) -> bool {
    (((((x27 < 100) && (x28 < 100)) && (0 < x27)) && (0 < x28)) && (((x27 * x28) > 0) && x26@.len()
        >= (x27 * x28) - 1 + 1))
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn index_(x0: i32, x1: i32, x2: i32, x3: i32) -> (result: i32)
    requires
        ((((((((0 < x0) && (x0 < 100)) && (0 < x1)) && (x1 < 100)) && (0 <= x2)) && (0 <= x3)) && (
        x2 < x0)) && (x3 < x1)),
    ensures
        ((0 <= result) && (result < (x0 * x1))),
{
    let x5: i32 = x2 * x1;
    let x6: i32 = x5 + x3;
    x6
}

fn CheckPre_index_(x0: i32, x1: i32, x2: i32, x3: i32)
    requires
        ((((((((0 < x0) && (x0 < 100)) && (0 < x1)) && (x1 < 100)) && (0 <= x2)) && (0 <= x3)) && (
        x2 < x0)) && (x3 < x1)),
{}

fn CheckPost_index_(x0: i32, x1: i32, x2: i32, x3: i32, result: i32)
    requires
        ((0 <= result) && (result < (x0 * x1))),
{}

fn CheckPre_mult(
    x63: &[i32],
    x64: i32,
    x65: i32,
    x66: &[i32],
    x67: i32,
    x68: i32,
    old_x69: &[i32],
    x70: i32,
    x71: i32,
)
    requires
        ((((inv_matrix_Boolean(x63, x64 as int, x65 as int)) && (inv_matrix_Boolean(
            x66,
            x67 as int,
            x68 as int,
        ))) && (inv_matrix_Boolean(old_x69, x70 as int, x71 as int))) && (((x65 == x67) && (x64
            == x70)) && (x68 == x71))),
{}

fn CheckPost_mult(
    x63: &[i32],
    x64: i32,
    x65: i32,
    x66: &[i32],
    x67: i32,
    x68: i32,
    x69: &[i32],
    x70: i32,
    x71: i32,
)
    requires
        (((inv_matrix_Boolean(x63, x64 as int, x65 as int)) && (inv_matrix_Boolean(
            x66,
            x67 as int,
            x68 as int,
        ))) && (inv_matrix_Boolean(x69, x70 as int, x71 as int))),
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn mult(
    x63: &[i32],
    x64: i32,
    x65: i32,
    x66: &[i32],
    x67: i32,
    x68: i32,
    x69: &mut [i32],
    x70: i32,
    x71: i32,
)
    requires
        ((((inv_matrix_Boolean(x63, x64 as int, x65 as int)) && (inv_matrix_Boolean(
            x66,
            x67 as int,
            x68 as int,
        ))) && (inv_matrix_Boolean(old(x69), x70 as int, x71 as int))) && (((x65 == x67) && (x64
            == x70)) && (x68 == x71))),
    ensures
        (((inv_matrix_Boolean(x63, x64 as int, x65 as int)) && (inv_matrix_Boolean(
            x66,
            x67 as int,
            x68 as int,
        ))) && (inv_matrix_Boolean(x69, x70 as int, x71 as int))),
{
    let mut x76: i32 = 0;
    while x76 < x64
        invariant
            x69@.len() >= (x70 * x71) - 1 + 1, //2c
            0 <= x76 <= x64,
        decreases x64 - x76,
    {
        let mut x78: i32 = 0;
        while x78 < x68
            invariant
                x69@.len() >= (x70 * x71) - 1 + 1, //2c
                0 <= x78 <= x68,
            decreases x68 - x78,
        {
            let x79: i32 = index_(x70, x71, x76, x78);
            x69[x79 as usize] = 0;
            let mut x82: i32 = 0;
            while x82 < x65
                invariant
                    x69@.len() >= (x70 * x71) - 1 + 1, //2c
                    0 <= x82 <= x65,
                decreases x65 - x82,
            {
                let x83: i32 = x69[x79 as usize];
                let x84: i32 = index_(x64, x65, x76, x82);
                let x85: i32 = x63[x84 as usize];
                let x88: i32;
                if x85 != 0 {
                    let x86: i32 = index_(x67, x68, x82, x78);
                    let x87: i32 = x66[x86 as usize];
                    x88 = x87;
                } else {
                    x88 = 0;
                }
                let x89: i32 = if (x83 != 0) || (x88 != 0) {
                    1
                } else {
                    0
                };
                x69[x79 as usize] = x89;
                x82 += 1;
            }
            x78 += 1;
        }
        x76 += 1;
    }
}

fn main() {
}

fn valid_test_harness_index_() {
    // Test case 1: Valid - typical values
    CheckPre_index_(5, 5, 2, 3);
    let result1 = 13; // Expected: 2 * 5 + 3
    CheckPost_index_(5, 5, 2, 3, result1);

    // Test case 2: Valid - minimum x2 and x3
    CheckPre_index_(10, 20, 0, 0);
    let result2 = 0;
    CheckPost_index_(10, 20, 0, 0, result2);

    // Test case 3: Valid - mid-range values
    CheckPre_index_(2, 3, 1, 2);
    let result3 = 5; // Expected: 1 * 3 + 2
    CheckPost_index_(2, 3, 1, 2, result3);

    // Test case 4: Boundary - minimum dimensions
    CheckPre_index_(1, 1, 0, 0);
    let result4 = 0;
    CheckPost_index_(1, 1, 0, 0, result4);

    // Test case 5: Boundary - maximum dimensions
    CheckPre_index_(99, 99, 98, 98);
    let result5 = 9800; // Expected: 98 * 99 + 98
    CheckPost_index_(99, 99, 98, 98, result5);

    // Test case 8: Valid - another valid case
    CheckPre_index_(3, 4, 2, 3);
    let result8 = 11; // Expected: 2 * 4 + 3
    CheckPost_index_(3, 4, 2, 3, result8);

    // Test case 9: Valid - mid-range values
    CheckPre_index_(50, 50, 25, 25);
    let result9 = 1275; // Expected: 25 * 50 + 25
    CheckPost_index_(50, 50, 25, 25, result9);
}

fn invalid_test_harness_index_() {
    // Test case 6: Invalid - x0 <= 0
    CheckPre_index_(0, 5, 0, 3);

    // Test case 7: Invalid - x3 >= x1 (Column index out of bounds)
    CheckPre_index_(5, 5, 2, 5);
}

fn valid_test_harness_mult() {
    // Case 10: Identity * Matrix
    let (A10, B10) = ([1, 0, 0, 1], [1, 1, 0, 1]);
    let mut C10 = [0; 4];
    CheckPre_mult(&A10, 2, 2, &B10, 2, 2, &C10, 2, 2);
    let result10 = [1, 1, 0, 1];
    CheckPost_mult(&A10, 2, 2, &B10, 2, 2, &result10, 2, 2);

    // Case 11: Zero * Matrix
    let (A11, B11) = ([0, 0, 0, 0], [1, 1, 1, 1]);
    let mut C11 = [0; 4];
    CheckPre_mult(&A11, 2, 2, &B11, 2, 2, &C11, 2, 2);
    let result11 = [0, 0, 0, 0];
    CheckPost_mult(&A11, 2, 2, &B11, 2, 2, &result11, 2, 2);

    // Case 12: Rectangular
    let (A12, B12) = ([1, 0, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1]);
    let mut C12 = [0; 4];
    CheckPre_mult(&A12, 2, 3, &B12, 3, 2, &C12, 2, 2);
    let result12 = [1, 1, 1, 1];
    CheckPost_mult(&A12, 2, 3, &B12, 3, 2, &result12, 2, 2);

    // Case 13: 1x1
    let (A13, B13) = ([1], [1]);
    let mut C13 = [0; 1];
    CheckPre_mult(&A13, 1, 1, &B13, 1, 1, &C13, 1, 1);
    let result13 = [1];
    CheckPost_mult(&A13, 1, 1, &B13, 1, 1, &result13, 1, 1);

    // Case 14: 1x2 * 2x1
    let (A14, B14) = ([1, 1], [1, 1]);
    let mut C14 = [0; 1];
    CheckPre_mult(&A14, 1, 2, &B14, 2, 1, &C14, 1, 1);
    let result14 = [1];
    CheckPost_mult(&A14, 1, 2, &B14, 2, 1, &result14, 1, 1);

    // Case 15: 3x1 * 1x3
    let (A15, B15) = ([1, 0, 1], [1, 1, 1]);
    let mut C15 = [0; 9];
    CheckPre_mult(&A15, 3, 1, &B15, 1, 3, &C15, 3, 3);
    let result15 = [1, 1, 1, 0, 0, 0, 1, 1, 1];
    CheckPost_mult(&A15, 3, 1, &B15, 1, 3, &result15, 3, 3);

    // Case 16: Sparse Result
    let (A16, B16) = ([1, 0, 0, 0], [0, 0, 0, 1]);
    let mut C16 = [0; 4];
    CheckPre_mult(&A16, 2, 2, &B16, 2, 2, &C16, 2, 2);
    let result16 = [0, 0, 0, 0];
    CheckPost_mult(&A16, 2, 2, &B16, 2, 2, &result16, 2, 2);
}

fn invalid_test_harness_mult() {
    // Case 17: Inner Dimension Mismatch
    let (A, B, C) = ([0;4], [0;4], [0;4]);
    CheckPre_mult(&A, 2, 2, &B, 3, 2, &C, 2, 2); // Panics on x65 != x67

    // Case 18: Dimensions >= 100
    CheckPre_mult(&A, 100, 2, &B, 2, 2, &C, 100, 2); // Panics on x64 < 100
}

} // verus!

// RAC

// fn index_(x0: i32, x1: i32, x2: i32, x3: i32) -> i32
// {
//     let x5: i32 = x2 * x1;
//     let x6: i32 = x5 + x3;
//     x6
// }


// fn mult(
//     x63: &[i32],
//     x64: i32,
//     x65: i32,
//     x66: &[i32],
//     x67: i32,
//     x68: i32,
//     x69: &mut [i32],
//     x70: i32,
//     x71: i32,
// )
// {
//     let mut x76: i32 = 0;
//     while x76 < x64
//     {
//         let old_measure = x64 - x76;
//         assert!(
//             x69.len() as i32 >= (x70 * x71) - 1 + 1 &&
//             0 <= x76 && x76 <= x64
//         );
//         let mut x78: i32 = 0;
//         while x78 < x68
//         {
//             let old_measure2 = x68 - x78;
//             assert!(
//                 x69.len() as i32 >= (x70 * x71) - 1 + 1 &&
//                 0 <= x78 && x78 <= x68
//             );
//             let x79: i32 = index_(x70, x71, x76, x78);
//             x69[x79 as usize] = 0;
//             let mut x82: i32 = 0;
//             while x82 < x65
//             {
//                 let old_measure3 = x65 - x82;
//                 assert!(
//                     x69.len() as i32 >= (x70 * x71) - 1 + 1 &&
//                     0 <= x82 && x82 <= x65
//                 );
//                 let x83: i32 = x69[x79 as usize];
//                 let x84: i32 = index_(x64, x65, x76, x82);
//                 let x85: i32 = x63[x84 as usize];
//                 let x88: i32;
//                 if x85 != 0 {
//                     let x86: i32 = index_(x67, x68, x82, x78);
//                     let x87: i32 = x66[x86 as usize];
//                     x88 = x87;
//                 } else {
//                     x88 = 0;
//                 }
//                 let x89: i32 = if (x83 != 0) || (x88 != 0) {
//                     1
//                 } else {
//                     0
//                 };
//                 x69[x79 as usize] = x89;
//                 x82 += 1;
//                 assert!(old_measure3 > x65 - x82);
//             }
//             assert!(
//                 x69.len() as i32 >= (x70 * x71) - 1 + 1 &&
//                 0 <= x82 && x82 <= x65
//             );
//             x78 += 1;
//             assert!(old_measure2 > x68 - x78);
//         }
//         assert!(
//             x69.len() as i32 >= (x70 * x71) - 1 + 1 &&
//             0 <= x78 && x78 <= x68
//         );
//         x76 += 1;
//         assert!(old_measure > x64 - x76);
//     }
//     assert!(
//         x69.len() as i32 >= (x70 * x71) - 1 + 1 &&
//         0 <= x76 && x76 <= x64
//     );
// }

// fn main() {
//     valid_test_harness_mult();
// }

// fn valid_test_harness_mult() {
//     // Case 10: Identity * Matrix
//     let (A10, B10) = ([1, 0, 0, 1], [1, 1, 0, 1]);
//     let mut C10 = [0; 4];
//     mult(&A10, 2, 2, &B10, 2, 2, &mut C10, 2, 2);

//     // Case 11: Zero * Matrix
//     let (A11, B11) = ([0, 0, 0, 0], [1, 1, 1, 1]);
//     let mut C11 = [0; 4];
//     mult(&A11, 2, 2, &B11, 2, 2, &mut C11, 2, 2);

//     // Case 12: Rectangular
//     let (A12, B12) = ([1, 0, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1]);
//     let mut C12 = [0; 4];
//     mult(&A12, 2, 3, &B12, 3, 2, &mut C12, 2, 2);

//     // Case 13: 1x1
//     let (A13, B13) = ([1], [1]);
//     let mut C13 = [0; 1];
//     mult(&A13, 1, 1, &B13, 1, 1, &mut C13, 1, 1);

//     // Case 14: 1x2 * 2x1
//     let (A14, B14) = ([1, 1], [1, 1]);
//     let mut C14 = [0; 1];
//     mult(&A14, 1, 2, &B14, 2, 1, &mut C14, 1, 1);

//     // Case 15: 3x1 * 1x3
//     let (A15, B15) = ([1, 0, 1], [1, 1, 1]);
//     let mut C15 = [0; 9];
//     mult(&A15, 3, 1, &B15, 1, 3, &mut C15, 3, 3);

//     // Case 16: Sparse Result
//     let (A16, B16) = ([1, 0, 0, 0], [0, 0, 0, 1]);
//     let mut C16 = [0; 4];
//     mult(&A16, 2, 2, &B16, 2, 2, &mut C16, 2, 2);
// }