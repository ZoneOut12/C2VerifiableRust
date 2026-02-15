#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

spec fn ge_zero(x: i32) -> bool { //2A
    x >= 0 //2A
}//2A

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
        ((((((inv_matrix_Boolean(x63, x64 as int, x65 as int)) && (inv_matrix_Boolean(
            x66,
            x67 as int,
            x68 as int,
        ))) && (inv_matrix_Boolean(old_x69, x70 as int, x71 as int))) && ((x70 == x64) && (x71
            == x65))) && ((x70 == x67) && (x71 == x68))) && ((forall|x121: i32|
            (forall|x122: i32|
                ((((#[trigger] ge_zero(x121) && (x121 < (x70 * x71))) && (#[trigger] ge_zero(x122) && (x122 < (x64//2B
                    * x65))))) as int != 0 ==> (true) as int != 0))) && (forall|x136: i32|
            (forall|x137: i32|
                ((((#[trigger] ge_zero(x136) && (x136 < (x70 * x71))) && (#[trigger] ge_zero(x137) && (x137 < (x67//2B
                    * x68))))) as int != 0 ==> (true) as int != 0))))),
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
        ((((inv_matrix_Boolean(x63, x64 as int, x65 as int)) && (inv_matrix_Boolean(
            x66,
            x67 as int,
            x68 as int,
        ))) && (inv_matrix_Boolean(x69, x70 as int, x71 as int))) && (forall|x157: i32|
            ((((0 <= x157) && (x157 < (x70 * x71)))) as int != 0 ==> ((x69@[(x157) as int] == (
            x63@[(x157) as int] != 0 || x66@[(x157) as int] != 0) as int)) as int != 0))),//1
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
        ((((((inv_matrix_Boolean(x63, x64 as int, x65 as int)) && (inv_matrix_Boolean(
            x66,
            x67 as int,
            x68 as int,
        ))) && (inv_matrix_Boolean(old(x69), x70 as int, x71 as int))) && ((x70 == x64) && (x71
            == x65))) && ((x70 == x67) && (x71 == x68))) && ((forall|x121: i32|
            (forall|x122: i32|
                ((((#[trigger] ge_zero(x121) && (x121 < (x70 * x71))) && (#[trigger] ge_zero(x122) && (x122 < (x64//2B
                    * x65))))) as int != 0 ==> (true) as int != 0))) && (forall|x136: i32|
            (forall|x137: i32|
                ((((#[trigger] ge_zero(x136) && (x136 < (x70 * x71))) && (#[trigger] ge_zero(x137) && (x137 < (x67//2B
                    * x68))))) as int != 0 ==> (true) as int != 0))))),
    ensures
        ((((inv_matrix_Boolean(x63, x64 as int, x65 as int)) && (inv_matrix_Boolean(
            x66,
            x67 as int,
            x68 as int,
        ))) && (inv_matrix_Boolean(x69, x70 as int, x71 as int))) && (forall|x157: i32|
            ((((0 <= x157) && (x157 < (x70 * x71)))) as int != 0 ==> ((x69@[(x157) as int] == (
            x63@[(x157) as int] != 0 || x66@[(x157) as int] != 0) as int)) as int != 0))),//1
{
    assert(true);
    assert(true);
    let x73: i32 = x70 * x71;
    let mut x81: i32 = 0;
    while x81 < x73
        invariant
            x69@.len() >= (x70 * x71) - 1 + 1, //2C
            0 <= x81 <= x73,
            (forall|x82: i32|
                ((((0 <= x82) && (x82 < x81))) as int != 0 ==> ((x69@[(x82) as int] == (x63@[(
                x82) as int] !=0 || x66@[(x82) as int] !=0) as int)) as int != 0)),//1
        decreases x73 - x81,
    {
        let x94: i32 = x63[x81 as usize];
        let x95: i32 = x66[x81 as usize];
        let x96: i32 = if x94 != 0 || x95 != 0 {
            1
        } else {
            0
        };
        x69[x81 as usize] = x96;
        assert(true);
        assert(true);
        x81 += 1;
    }
}

fn CheckPre_scalar_mult(
    x171: i32,
    x172: &[i32],
    x173: i32,
    x174: i32,
    old_x175: &[i32],
    x176: i32,
    x177: i32,
)
    requires
        ((((inv_matrix_Boolean(x172, x173 as int, x174 as int)) && (inv_matrix_Boolean(
            old_x175,
            x176 as int,
            x177 as int,
        ))) && ((x176 == x173) && (x177 == x174))) && (forall|x213: i32|
            (forall|x214: i32|
                ((((#[trigger] ge_zero(x213) && (x213 < (x176 * x177))) && (#[trigger] ge_zero(x214) && (x214 < (x173//2B
                    * x174))))) as int != 0 ==> (true) as int != 0)))),
        forall|i: i32|
            (0 <= i < x173 * x174) as int != 0 ==> (x172@[(i) as int] == 0 || x172@[(i) as int]
                == 1) as int != 0,
{}

fn CheckPost_scalar_mult(
    x171: i32,
    x172: &[i32],
    x173: i32,
    x174: i32,
    x175: &[i32],
    x176: i32,
    x177: i32,
)
    requires
        ((((inv_matrix_Boolean(x172, x173 as int, x174 as int)) && (inv_matrix_Boolean(
            x175,
            x176 as int,
            x177 as int,
        ))) && (forall|x233: i32|
            ((((0 <= x233) && (x233 < (x176 * x177)))) as int != 0 ==> ((x175@[(x233) as int] == (
            x171 !=0 && x172@[(x233) as int] != 0) as int)) as int != 0))) && (((x171 != 0 == false)) as int != 0 ==> ((//1
        forall|x247: i32|
            ((#[trigger] ge_zero(x247) && x247 < x176)) as int != 0 ==> ((forall|x250: i32|//2B
                ((#[trigger] ge_zero(x250) && x250 < x177)) as int != 0 ==> ((x175@[(((x247 * x177) + x250)) as int] !=0//1 //2B
                    == false)) as int != 0)) as int != 0)) as int != 0)),
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn scalar_mult(
    x171: i32,
    x172: &[i32],
    x173: i32,
    x174: i32,
    x175: &mut [i32],
    x176: i32,
    x177: i32,
)
    requires
        ((((inv_matrix_Boolean(x172, x173 as int, x174 as int)) && (inv_matrix_Boolean(
            old(x175),
            x176 as int,
            x177 as int,
        ))) && ((x176 == x173) && (x177 == x174))) && (forall|x213: i32|
            (forall|x214: i32|
                ((((#[trigger] ge_zero(x213) && (x213 < (x176 * x177))) && (#[trigger] ge_zero(x214) && (x214 < (x173//2B
                    * x174))))) as int != 0 ==> (true) as int != 0)))),
        forall|i: i32|
            (0 <= i < x173 * x174) as int != 0 ==> (x172@[(i) as int] == 0 || x172@[(i) as int]
                == 1) as int != 0,
    ensures
        ((((inv_matrix_Boolean(x172, x173 as int, x174 as int)) && (inv_matrix_Boolean(
            x175,
            x176 as int,
            x177 as int,
        ))) && (forall|x233: i32|
            ((((0 <= x233) && (x233 < (x176 * x177)))) as int != 0 ==> ((x175@[(x233) as int] == (
            x171 !=0 && x172@[(x233) as int] != 0) as int)) as int != 0))) && (((x171 != 0 == false)) as int != 0 ==> ((//1
        forall|x247: i32|
            ((#[trigger] ge_zero(x247) && x247 < x176)) as int != 0 ==> ((forall|x250: i32|//2B
                ((#[trigger] ge_zero(x250) && x250 < x177)) as int != 0 ==> ((x175@[(((x247 * x177) + x250)) as int] !=0//1 //2B
                    == false)) as int != 0)) as int != 0)) as int != 0)),
{
    assert(true);
    let x179: i32 = x176 * x177;
    let mut x184: i32 = 0;
    while x184 < x179
        invariant
            x175@.len() >= (x176 * x177) - 1 + 1, //2C
            0 <= x184 <= x179,
            (forall|x185: i32|
                ((((0 <= x185) && (x185 < x184))) as int != 0 ==> ((x175@[(x185) as int] == (x171 !=0//1
                    && x172@[(x185) as int] != 0) as int)) as int != 0)), //1
        decreases x179 - x184,
    {
        let x197: i32;
        if x171 != 0 {
            let x196: i32 = x172[x184 as usize];
            x197 = x196;
        } else {
            x197 = 0;
        }
        x175[x184 as usize] = x197;
        assert(true);
        x184 += 1;
    }
}

fn main() {
}

fn valid_test_harness_index_() {
    // Test case 1: Valid - normal case
    CheckPre_index_(5, 10, 3, 5);
    let result1 = 35; // Hardcoded Expected: 3 * 10 + 5
    CheckPost_index_(5, 10, 3, 5, result1);

    // Test case 2: Valid - maximum dimensions
    CheckPre_index_(99, 99, 98, 98);
    let result2 = 9800; // Hardcoded Expected: 98 * 99 + 98
    CheckPost_index_(99, 99, 98, 98, result2);

    // Test case 3: Valid - minimal dimensions with edge values
    CheckPre_index_(2, 2, 0, 1);
    let result3 = 1; // Hardcoded Expected: 0 * 2 + 1
    CheckPost_index_(2, 2, 0, 1, result3);

    // Test case 4: Valid - mid-range values
    CheckPre_index_(10, 20, 5, 15);
    let result4 = 115; // Hardcoded Expected: 5 * 20 + 15
    CheckPost_index_(10, 20, 5, 15, result4);

    // Test case 5: Valid - minimal dimensions
    CheckPre_index_(1, 1, 0, 0);
    let result5 = 0; // Hardcoded Expected: 0 * 1 + 0
    CheckPost_index_(1, 1, 0, 0, result5);

    // Test case 8: Boundary - minimal dimensions (Duplicate of case 5 logic)
    CheckPre_index_(1, 1, 0, 0);
    let result8 = 0;
    CheckPost_index_(1, 1, 0, 0, result8);

    // Test case 9: Boundary - maximum allowed values (Duplicate of case 2 logic)
    CheckPre_index_(99, 99, 98, 98);
    let result9 = 9800;
    CheckPost_index_(99, 99, 98, 98, result9);
}

fn invalid_test_harness_index_() {
    // Test case 6: Invalid - x0=0 (Violates 0 < x0)
    // This call is expected to trigger a panic in CheckPre
    CheckPre_index_(0, 5, 0, 0);

    // Test case 7: Invalid - x2 >= x0 and x3 >= x1
    // This call is expected to trigger a panic in CheckPre
    CheckPre_index_(5, 5, 5, 5);
}

// ========== Rust Test Harness for add and scalar_mult ==========

fn valid_test_harness_add() {
    // 1. Normal 2x2 addition (OR logic)
    let a1 = [1, 0, 0, 1]; let b1 = [0, 1, 0, 1];
    let res1 = [1, 1, 0, 1];
    CheckPre_add(&a1, 2, 2, &b1, 2, 2, &res1, 2, 2);
    CheckPost_add(&a1, 2, 2, &b1, 2, 2, &res1, 2, 2);

    // 2. All zeros
    let a2 = [0, 0]; let b2 = [0, 0];
    let res2 = [0, 0];
    CheckPre_add(&a2, 1, 2, &b2, 1, 2, &res2, 1, 2);
    CheckPost_add(&a2, 1, 2, &b2, 1, 2, &res2, 1, 2);

    // 3. All ones (1 || 1 = 1)
    let a3 = [1, 1]; let b3 = [1, 1];
    let res3 = [1, 1];
    CheckPre_add(&a3, 1, 2, &b3, 1, 2, &res3, 1, 2);
    CheckPost_add(&a3, 1, 2, &b3, 1, 2, &res3, 1, 2);

    // 4. 1x1 Boundary
    let a4 = [0]; let b4 = [1];
    let res4 = [1];
    CheckPre_add(&a4, 1, 1, &b4, 1, 1, &res4, 1, 1);
    CheckPost_add(&a4, 1, 1, &b4, 1, 1, &res4, 1, 1);

    // 5. Rectangular 3x2
    let a5 = [1, 0, 0, 1, 1, 1]; let b5 = [0, 0, 1, 1, 0, 0];
    let res5 = [1, 0, 1, 1, 1, 1];
    CheckPre_add(&a5, 3, 2, &b5, 3, 2, &res5, 3, 2);
    CheckPost_add(&a5, 3, 2, &b5, 3, 2, &res5, 3, 2);

    // 6. Max dimensions (99x1)
    let mut a6 = [0; 99]; a6[98] = 1;
    let b6 = [0; 99];
    let mut res6 = [0; 99]; res6[98] = 1;
    CheckPre_add(&a6, 99, 1, &b6, 99, 1, &res6, 99, 1);
    CheckPost_add(&a6, 99, 1, &b6, 99, 1, &res6, 99, 1);

    // 7. Identity-like (A + Zero = A)
    let a7 = [1, 0, 1]; let b7 = [0, 0, 0];
    let res7 = [1, 0, 1];
    CheckPre_add(&a7, 1, 3, &b7, 1, 3, &res7, 1, 3);
    CheckPost_add(&a7, 1, 3, &b7, 1, 3, &res7, 1, 3);
}

fn invalid_test_harness_add() {
    let dummy = [0; 4];
    // 8. Invalid: Dimension mismatch (x64 != x67)
    CheckPre_add(&dummy, 2, 2, &dummy, 1, 4, &dummy, 2, 2);

    // 9. Invalid: Out of ACSL range (x64 >= 100)
    CheckPre_add(&dummy, 105, 1, &dummy, 105, 1, &dummy, 105, 1);
}

fn valid_test_harness_scalar_mult() {
    // 1. Scalar 1 (Identity)
    let a1 = [1, 0, 1, 1];
    let res1 = [1, 0, 1, 1];
    CheckPre_scalar_mult(1, &a1, 2, 2, &res1, 2, 2);
    CheckPost_scalar_mult(1, &a1, 2, 2, &res1, 2, 2);

    // 2. Scalar 0 (Nullify)
    let a2 = [1, 1, 1, 1];
    let res2 = [0, 0, 0, 0];
    CheckPre_scalar_mult(0, &a2, 2, 2, &res2, 2, 2);
    CheckPost_scalar_mult(0, &a2, 2, 2, &res2, 2, 2);

    // 3. 1x1 Boundary
    let a3 = [1]; let res3 = [1];
    CheckPre_scalar_mult(1, &a3, 1, 1, &res3, 1, 1);
    CheckPost_scalar_mult(1, &a3, 1, 1, &res3, 1, 1);

    // 4. All zeros input
    let a4 = [0, 0, 0]; let res4 = [0, 0, 0];
    CheckPre_scalar_mult(1, &a4, 1, 3, &res4, 1, 3);
    CheckPost_scalar_mult(1, &a4, 1, 3, &res4, 1, 3);

    // 5. Rectangular 2x3
    let a5 = [1, 1, 1, 0, 0, 0]; let res5 = [1, 1, 1, 0, 0, 0];
    CheckPre_scalar_mult(1, &a5, 2, 3, &res5, 2, 3);
    CheckPost_scalar_mult(1, &a5, 2, 3, &res5, 2, 3);

    // 6. Max dimensions (1x99)
    let mut a6 = [0; 99]; a6[0] = 1;
    let mut res6 = [0; 99]; res6[0] = 1;
    CheckPre_scalar_mult(1, &a6, 1, 99, &res6, 1, 99);
    CheckPost_scalar_mult(1, &a6, 1, 99, &res6, 1, 99);

    // 7. Scalar 1 on sparse matrix
    let a7 = [0, 0, 1, 0]; let res7 = [0, 0, 1, 0];
    CheckPre_scalar_mult(1, &a7, 2, 2, &res7, 2, 2);
    CheckPost_scalar_mult(1, &a7, 2, 2, &res7, 2, 2);
}

fn invalid_test_harness_scalar_mult() {
    let dummy = [0; 4];
    // 8. Invalid: Dimension violation (x112 <= 0)
    CheckPre_scalar_mult(1, &dummy, 0, 2, &dummy, 0, 2);

    // 9. Invalid: Out of ACSL range (x112 >= 100)
    CheckPre_scalar_mult(1, &dummy, 100, 1, &dummy, 100, 1);
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
//     assert!(true);
//     assert!(true);
//     let x73: i32 = x70 * x71;
//     let mut x81: i32 = 0;
//     while x81 < x73
//     {
//         let old_measure = x73 - x81;
//         assert!(
//             x69.len() as i32 >= (x70 * x71) - 1 + 1 && //2C
//             0 <= x81 && x81 <= x73 &&
//             (0..x81).all(|x82| (x69[(x82) as usize] == (x63[(
//                 x82) as usize] != 0 || x66[(x82) as usize] != 0) as i32))
//         );
//         let x94: i32 = x63[x81 as usize];
//         let x95: i32 = x66[x81 as usize];
//         let x96: i32 = if x94 != 0 || x95 != 0 {
//             1
//         } else {
//             0
//         };
//         x69[x81 as usize] = x96;
//         assert!(true);
//         assert!(true);
//         x81 += 1;
//         assert!(old_measure > x73 - x81);
//     }
//     assert!(
//         x69.len() as i32 >= (x70 * x71) - 1 + 1 && //2C
//         0 <= x81 && x81 <= x73 &&
//         (0..x81).all(|x82| (x69[(x82) as usize] == (x63[(
//             x82) as usize] != 0 || x66[(x82) as usize] != 0) as i32))
//     );
// }

// fn scalar_mult(
//     x171: i32,
//     x172: &[i32],
//     x173: i32,
//     x174: i32,
//     x175: &mut [i32],
//     x176: i32,
//     x177: i32,
// )
// {
//     assert!(true);
//     let x179: i32 = x176 * x177;
//     let mut x184: i32 = 0;
//     while x184 < x179
//     {
//         let old_measure = x179 - x184;
//         assert!(
//             x175.len() as i32 >= (x176 * x177) - 1 + 1 &&
//             0 <= x184 && x184 <= x179 &&
//             (1..x184).all(|x185| x175[(x185) as usize] == ((x171 != 0//1
//                     && x172[(x185) as usize] != 0)) as i32)
//         );
//         let x197: i32;
//         if x171 != 0 {
//             let x196: i32 = x172[x184 as usize];
//             x197 = x196;
//         } else {
//             x197 = 0;
//         }
//         x175[x184 as usize] = x197;
//         assert!(true);
//         x184 += 1;
//         assert!(old_measure > x179 - x184);
//     }
//     assert!(
//         (x175.len() as i32) >= ((x176 * x177) - 1 + 1) &&
//         0 <= x184 && x184 <= x179 &&
//         (1..x184).all(|x185| x175[(x185) as usize] == (x171 != 0//1
//                 && x172[(x185) as usize] != 0) as i32)
//     );
// }

// fn main() {
//     valid_test_harness_index_();
//     valid_test_harness_add();
//     valid_test_harness_scalar_mult();
// }

// fn valid_test_harness_index_() {
//     // Test case 1: Valid - normal case
//     index_(5, 10, 3, 5);

//     // Test case 2: Valid - maximum dimensions
//     index_(99, 99, 98, 98);

//     // Test case 3: Valid - minimal dimensions with edge values
//     index_(2, 2, 0, 1);

//     // Test case 4: Valid - mid-range values
//     index_(10, 20, 5, 15);

//     // Test case 5: Valid - minimal dimensions
//     index_(1, 1, 0, 0);

//     // Test case 8: Boundary - minimal dimensions (Duplicate of case 5 logic)
//     index_(1, 1, 0, 0);

//     // Test case 9: Boundary - maximum allowed values (Duplicate of case 2 logic)
//     index_(99, 99, 98, 98);
// }

// // ========== Rust Test Harness for add and scalar_mult ==========

// fn valid_test_harness_add() {
//     // 1. Normal 2x2 addition (OR logic)
//     let a1 = [1, 0, 0, 1]; let b1 = [0, 1, 0, 1];
//     let mut res1 = [1, 1, 0, 1];
//     add(&a1, 2, 2, &b1, 2, 2, &mut res1, 2, 2);

//     // 2. All zeros
//     let a2 = [0, 0]; let b2 = [0, 0];
//     let mut res2 = [0, 0];
//     add(&a2, 1, 2, &b2, 1, 2, &mut res2, 1, 2);

//     // 3. All ones (1 || 1 = 1)
//     let a3 = [1, 1]; let b3 = [1, 1];
//     let mut res3 = [1, 1];
//     add(&a3, 1, 2, &b3, 1, 2, &mut res3, 1, 2);

//     // 4. 1x1 Boundary
//     let a4 = [0]; let b4 = [1];
//     let mut res4 = [1];
//     add(&a4, 1, 1, &b4, 1, 1, &mut res4, 1, 1);

//     // 5. Rectangular 3x2
//     let a5 = [1, 0, 0, 1, 1, 1]; let b5 = [0, 0, 1, 1, 0, 0];
//     let mut res5 = [1, 0, 1, 1, 1, 1];
//     add(&a5, 3, 2, &b5, 3, 2, &mut res5, 3, 2);

//     // 6. Max dimensions (99x1)
//     let mut a6 = [0; 99]; a6[98] = 1;
//     let b6 = [0; 99];
//     let mut res6 = [0; 99]; res6[98] = 1;
//     add(&a6, 99, 1, &b6, 99, 1, &mut res6, 99, 1);

//     // 7. Identity-like (A + Zero = A)
//     let a7 = [1, 0, 1]; let b7 = [0, 0, 0];
//     let mut res7 = [1, 0, 1];
//     add(&a7, 1, 3, &b7, 1, 3, &mut res7, 1, 3);
// }

// fn valid_test_harness_scalar_mult() {
//     // 1. Scalar 1 (Identity)
//     let a1 = [1, 0, 1, 1];
//     let mut res1 = [1, 0, 1, 1];
//     scalar_mult(1, &a1, 2, 2, &mut res1, 2, 2);

//     // 2. Scalar 0 (Nullify)
//     let a2 = [1, 1, 1, 1];
//     let mut res2 = [0, 0, 0, 0];
//     scalar_mult(0, &a2, 2, 2, &mut res2, 2, 2);

//     // 3. 1x1 Boundary
//     let a3 = [1]; let mut res3 = [1];
//     scalar_mult(1, &a3, 1, 1, &mut res3, 1, 1);

//     // 4. All zeros input
//     let a4 = [0, 0, 0]; let mut res4 = [0, 0, 0];
//     scalar_mult(1, &a4, 1, 3, &mut res4, 1, 3);

//     // 5. Rectangular 2x3
//     let a5 = [1, 1, 1, 0, 0, 0]; let mut res5 = [1, 1, 1, 0, 0, 0];
//     scalar_mult(1, &a5, 2, 3, &mut res5, 2, 3);

//     // 6. Max dimensions (1x99)
//     let mut a6 = [0; 99]; a6[0] = 1;
//     let mut res6 = [0; 99]; res6[0] = 1;
//     scalar_mult(1, &a6, 1, 99, &mut res6, 1, 99);

//     // 7. Scalar 1 on sparse matrix
//     let a7 = [0, 0, 1, 0]; let mut res7 = [0, 0, 1, 0];
//     scalar_mult(1, &a7, 2, 2, &mut res7, 2, 2);
// }
