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

fn CheckPre_add(
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
        ))) && (inv_matrix_Boolean(old_x69, x70 as int, x71 as int))) && ((((x64 == x67) && (x64
            == x70)) && (x65 == x68)) && (x65 == x71))),
{}

fn CheckPost_add(
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
fn add(
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
        ))) && (inv_matrix_Boolean(old(x69), x70 as int, x71 as int))) && ((((x64 == x67) && (x64
            == x70)) && (x65 == x68)) && (x65 == x71))),
    ensures
        (((inv_matrix_Boolean(x63, x64 as int, x65 as int)) && (inv_matrix_Boolean(
            x66,
            x67 as int,
            x68 as int,
        ))) && (inv_matrix_Boolean(x69, x70 as int, x71 as int))),
{
    let mut x76: i32 = 0;
    while x76 < x70
        invariant
            x69@.len() >= (x70 * x71), //2c
            0 <= x76 <= x70,
        decreases x70 - x76,
    {
        let mut x78: i32 = 0;
        while x78 < x71
            invariant
                x69@.len() >= (x70 * x71), //2c
                0 <= x78 <= x71,
            decreases x71 - x78,
        {
            let x79: i32 = index_(x64, x65, x76, x78);
            let x80: i32 = x63[x79 as usize];
            let x81: i32 = index_(x67, x68, x76, x78);
            let x82: i32 = x66[x81 as usize];
            let x83: i32 = if (x80 != 0) || (x82 != 0) {
                1
            } else {
                0
            };
            let x84: i32 = index_(x70, x71, x76, x78);
            x69[x84 as usize] = x83;
            x78 += 1;
        }
        x76 += 1;
    }
}

fn CheckPre_scalar_mult(
    x110: i32,
    x111: &[i32],
    x112: i32,
    x113: i32,
    old_x114: &[i32],
    x115: i32,
    x116: i32,
)
    requires
        (((inv_matrix_Boolean(x111, x112 as int, x113 as int)) && (inv_matrix_Boolean(
            old_x114,
            x115 as int,
            x116 as int,
        ))) && ((x112 == x115) && (x113 == x116))),
{}

fn CheckPost_scalar_mult(
    x110: i32,
    x111: &[i32],
    x112: i32,
    x113: i32,
    x114: &[i32],
    x115: i32,
    x116: i32,
)
    requires
        ((inv_matrix_Boolean(x111, x112 as int, x113 as int)) && (inv_matrix_Boolean(
            x114,
            x115 as int,
            x116 as int,
        ))),
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn scalar_mult(
    x110: i32,
    x111: &[i32],
    x112: i32,
    x113: i32,
    x114: &mut [i32],
    x115: i32,
    x116: i32,
)
    requires
        (((inv_matrix_Boolean(x111, x112 as int, x113 as int)) && (inv_matrix_Boolean(
            old(x114),
            x115 as int,
            x116 as int,
        ))) && ((x112 == x115) && (x113 == x116))),
    ensures
        ((inv_matrix_Boolean(x111, x112 as int, x113 as int)) && (inv_matrix_Boolean(
            x114,
            x115 as int,
            x116 as int,
        ))),
{
    let mut x121: i32 = 0;
    while x121 < x115
        invariant
            x114@.len() >= (x115 * x116), //2c
            0 <= x121 <= x115,
        decreases x115 - x121,
    {
        let mut x123: i32 = 0;
        while x123 < x116
            invariant
                x114@.len() >= (x115 * x116), //2c
                0 <= x123 <= x116,
            decreases x116 - x123,
        {
            let x126: i32;
            if x110 != 0 {
                let x124: i32 = index_(x112, x113, x121, x123);
                let x125: i32 = x111[x124 as usize];
                x126 = x125;
            } else {
                x126 = 0;
            }
            let x127: i32 = index_(x115, x116, x121, x123);
            x114[x127 as usize] = x126;
            x123 += 1;
        }
        x121 += 1;
    }
}

fn main() {
}

fn valid_test_harness_matrix() {
    // Case 10: add() - Basic Addition
    let A10 = [1, 0];
    let B10 = [0, 1];
    let mut C10 = [0; 2];
    CheckPre_add(&A10, 1, 2, &B10, 1, 2, &C10, 1, 2);
    let result10 = [1, 1];
    CheckPost_add(&A10, 1, 2, &B10, 1, 2, &result10, 1, 2);

    // Case 13: scalar_mult() - Identity
    let A13 = [1, 0, 1, 0];
    let mut C13 = [0; 4];
    CheckPre_scalar_mult(1, &A13, 2, 2, &C13, 2, 2);
    let result13 = [1, 0, 1, 0];
    CheckPost_scalar_mult(1, &A13, 2, 2, &result13, 2, 2);

    // Case 14: scalar_mult() - Nullify
    let A14 = [1, 1, 1, 1];
    let mut C14 = [0; 4];
    CheckPre_scalar_mult(0, &A14, 2, 2, &C14, 2, 2);
    let result14 = [0, 0, 0, 0];
    CheckPost_scalar_mult(0, &A14, 2, 2, &result14, 2, 2);
}

fn invalid_test_harness_matrix() {
    let dummy = [0; 4];
    // Case 17: Dimension mismatch
    CheckPre_add(&dummy, 2, 2, &dummy, 3, 2, &dummy, 2, 2); 
    
    // Case 18: Dimension out of bounds
    CheckPre_scalar_mult(1, &dummy, 150, 1, &dummy, 150, 1);
}

} // verus!


// RAC
// fn index_(x0: i32, x1: i32, x2: i32, x3: i32) -> i32
// {
//     let x5: i32 = x2 * x1;
//     let x6: i32 = x5 + x3;
//     x6
// }

// fn add(
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
//     while x76 < x70
//     {
//         let old_measure = x70 - x76;
//         assert!(
//             x69.len() as i32 >= (x70 * x71) &&
//             0 <= x76 && x76 <= x70,
//         );
//         let mut x78: i32 = 0;
//         while x78 < x71
//         {
//             let old_measure2 = x71 - x78;
//             assert!(
//                 x69.len() as i32 >= (x70 * x71) &&
//                 0 <= x78 && x78 <= x71,
//             );
//             let x79: i32 = index_(x64, x65, x76, x78);
//             let x80: i32 = x63[x79 as usize];
//             let x81: i32 = index_(x67, x68, x76, x78);
//             let x82: i32 = x66[x81 as usize];
//             let x83: i32 = if (x80 != 0) || (x82 != 0) {
//                 1
//             } else {
//                 0
//             };
//             let x84: i32 = index_(x70, x71, x76, x78);
//             x69[x84 as usize] = x83;
//             x78 += 1;
//             assert!(old_measure2 > x71 - x78);
//         }
//         assert!(
//             x69.len() as i32 >= (x70 * x71) &&
//             0 <= x78 && x78 <= x71,
//         );
//         x76 += 1;
//         assert!(old_measure > x70 - x76);
//     }
//     assert!(
//         x69.len() as i32 >= (x70 * x71) &&
//         0 <= x76 && x76 <= x70,
//     );
// }

// fn scalar_mult(
//     x110: i32,
//     x111: &[i32],
//     x112: i32,
//     x113: i32,
//     x114: &mut [i32],
//     x115: i32,
//     x116: i32,
// )
// {
//     let mut x121: i32 = 0;
//     while x121 < x115
//     {
//         let old_measure = x115 - x121;
//         assert!(
//             x114.len() as i32 >= (x115 * x116) &&
//             0 <= x121 && x121 <= x115
//         );
//         let mut x123: i32 = 0;
//         while x123 < x116
//         {
//             let old_measure2 = x116 - x123;
//             assert!(
//                 x114.len() as i32 >= (x115 * x116) &&
//                 0 <= x123 && x123 <= x116
//             );
//             let x126: i32;
//             if x110 != 0 {
//                 let x124: i32 = index_(x112, x113, x121, x123);
//                 let x125: i32 = x111[x124 as usize];
//                 x126 = x125;
//             } else {
//                 x126 = 0;
//             }
//             let x127: i32 = index_(x115, x116, x121, x123);
//             x114[x127 as usize] = x126;
//             x123 += 1;
//             assert!( old_measure2 > x116 - x123);
//         }
//         assert!(
//             x114.len() as i32 >= (x115 * x116) &&
//             0 <= x123 && x123 <= x116
//         );
//         x121 += 1;
//         assert!(old_measure > x115 - x121);
//     }
//     assert!(
//         x114.len() as i32 >= (x115 * x116) &&
//         0 <= x121 && x121 <= x115
//     );
// }

// fn main() {
//     valid_test_harness_matrix();
// }

// fn valid_test_harness_matrix() {
//     // Case 10: add() - Basic Addition
//     let A10 = [1, 0];
//     let B10 = [0, 1];
//     let mut C10 = [0; 2];
//     add(&A10, 1, 2, &B10, 1, 2, &mut C10, 1, 2);

//     // Case 13: scalar_mult() - Identity
//     let A13 = [1, 0, 1, 0];
//     let mut C13 = [0; 4];
//     scalar_mult(1, &A13, 2, 2, &mut C13, 2, 2);

//     // Case 14: scalar_mult() - Nullify
//     let A14 = [1, 1, 1, 1];
//     let mut C14 = [0; 4];
//     scalar_mult(0, &A14, 2, 2, &mut C14, 2, 2);
// }
