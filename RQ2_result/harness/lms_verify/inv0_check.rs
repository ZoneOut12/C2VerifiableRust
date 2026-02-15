#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn inv_vec_Int(x0: &[i32], x1: int) -> bool {
    ((x1 == 0) || ((x1 > 0) && x0@.len() >= x1 - 1 + 1))
}

pub open spec fn ghost_eq_vec_Int(x15: &[i32], x16: i32, x17: &[i32], x18: i32) -> bool {//1
    ((x16 == x18) && (forall|x22: i32|
        ((0 <= x22 < x16)) as int != 0 ==> ((x15@[(x22) as int] == x17@[(x22) as int])) as int
            != 0))
}

fn CheckPre_eq_vec_Int(x15: &[i32], x16: i32, x17: &[i32], x18: i32)
    requires
        ((inv_vec_Int(x15, x16 as int)) && (inv_vec_Int(x17, x18 as int))),
{}

fn CheckPost_eq_vec_Int(x15: &[i32], x16: i32, x17: &[i32], x18: i32, result: i32)
    requires
        ((inv_vec_Int(x15, x16 as int)) && (inv_vec_Int(x17, x18 as int))),
        (result) as int != 0 <==> ((ghost_eq_vec_Int(x15, x16 as i32, x17, x18 as i32))) as int != 0,//1
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn eq_vec_Int(x15: &[i32], x16: i32, x17: &[i32], x18: i32) -> (result: i32)
    requires
        ((inv_vec_Int(x15, x16 as int)) && (inv_vec_Int(x17, x18 as int))),
    ensures
        ((inv_vec_Int(x15, x16 as int)) && (inv_vec_Int(x17, x18 as int))),
        (result) as int != 0 <==> ((ghost_eq_vec_Int(x15, x16 as i32, x17, x18 as i32))) as int != 0,//1
{
    let x20: i32 = if x16 == x18 {
        1
    } else {
        0
    };
    let x31: i32;
    if x20 != 0 {
        let mut x30: i32 = 1;
        let mut x23: i32 = 0;
        while x23 < x16
            invariant
                (0 <= x23 <= x16),
                forall|x22: i32|
                    ((0 <= x22 < x23)) as int != 0 ==> ((x15@[(x22) as int] == x17@[(
                    x22) as int])) as int != 0,
                x30 == 1,
            decreases (x16 - x23),
        {
            let x27: i32 = x15[x23 as usize];
            let x28: i32 = x17[x23 as usize];
            let x29: i32 = if x27 == x28 {
                1
            } else {
                0
            };
            if x29 == 0 {
                x30 = 0;
                break ;
            }
            x23 += 1;
        }
        x31 = x30;
    } else {
        x31 = 0;
    }
    x31
}

fn main() {
}

fn valid_test_harness() {
    // Test case 1: Identical arrays [1, 2, 3] vs [1, 2, 3]
    let v1_t1 = [1, 2, 3];
    let v2_t1 = [1, 2, 3];
    CheckPre_eq_vec_Int(&v1_t1, 3, &v2_t1, 3);
    let result1 = 1; // Expected: true
    CheckPost_eq_vec_Int(&v1_t1, 3, &v2_t1, 3, result1);

    // Test case 2: Different lengths (3 vs 2)
    let v1_t2 = [1, 2, 3];
    let v2_t2 = [1, 2];
    CheckPre_eq_vec_Int(&v1_t2, 3, &v2_t2, 2);
    let result2 = 0; // Expected: false
    CheckPost_eq_vec_Int(&v1_t2, 3, &v2_t2, 2, result2);

    // Test case 3: Same length, different values [1, 2, 3] vs [1, 5, 3]
    let v1_t3 = [1, 2, 3];
    let v2_t3 = [1, 5, 3];
    CheckPre_eq_vec_Int(&v1_t3, 3, &v2_t3, 3);
    let result3 = 0; // Expected: false
    CheckPost_eq_vec_Int(&v1_t3, 3, &v2_t3, 3, result3);

    // Test case 4: Single element boundary [42] vs [42]
    let v1_t4 = [42];
    let v2_t4 = [42];
    CheckPre_eq_vec_Int(&v1_t4, 1, &v2_t4, 1);
    let result4 = 1; // Expected: true
    CheckPost_eq_vec_Int(&v1_t4, 1, &v2_t4, 1, result4);

    // Test case 5: Boundary with Max/Min Integers
    let v1_t5 = [i32::MAX, i32::MIN];
    let v2_t5 = [i32::MAX, i32::MIN];
    CheckPre_eq_vec_Int(&v1_t5, 2, &v2_t5, 2);
    let result5 = 1; // Expected: true
    CheckPost_eq_vec_Int(&v1_t5, 2, &v2_t5, 2, result5);

    // Test case 6: Empty arrays (Size 0)
    let v1_t6: [i32; 0] = [];
    let v2_t6: [i32; 0] = [];
    CheckPre_eq_vec_Int(&v1_t6, 0, &v2_t6, 0);
    let result6 = 1; // Expected: true
    CheckPost_eq_vec_Int(&v1_t6, 0, &v2_t6, 0, result6);

    // Test case 7: Mismatch on the last element
    let v1_t7 = [10, 20, 30];
    let v2_t7 = [10, 20, 31];
    CheckPre_eq_vec_Int(&v1_t7, 3, &v2_t7, 3);
    let result7 = 0; // Expected: false
    CheckPost_eq_vec_Int(&v1_t7, 3, &v2_t7, 3, result7);
}

fn invalid_test_harness() {
    // Test case 8: Invalid - NULL equivalent / Out of bounds
    // In C, inv_vec_Int is false if pointer is NULL but size > 0
    let v1_err: [i32; 0] = [];
    let v2_err = [1, 2];
    CheckPre_eq_vec_Int(&v1_err, 5, &v2_err, 2);
}

} // verus!

// RAC
// fn eq_vec_Int(x15: &[i32], x16: i32, x17: &[i32], x18: i32) -> i32
// {
//     let x20: i32 = if x16 == x18 {
//         1
//     } else {
//         0
//     };
//     let x31: i32;
//     if x20 != 0 {
//         let mut x30: i32 = 1;
//         let mut x23: i32 = 0;
//         while x23 < x16
//         {
//             let old_measure = x16 - x23;
//             assert!(
//                 (0 <= x23 && x23 <= x16) &&
//                 (0..x23).all(|x22| x15[x22 as usize] == x17[x22 as usize]) &&
//                 x30 == 1
//             );  
//             let x27: i32 = x15[x23 as usize];
//             let x28: i32 = x17[x23 as usize];
//             let x29: i32 = if x27 == x28 {
//                 1
//             } else {
//                 0
//             };
//             if x29 == 0 {
//                 x30 = 0;
//                 break ;
//             }
//             x23 += 1;
//             assert!(old_measure > x16 - x23);
//         }
//         x31 = x30;
//     } else {
//         x31 = 0;
//     }
//     x31
// }

// fn main() {
//     valid_test_harness();
// }

// fn valid_test_harness() {
//     // Test case 1: Identical arrays [1, 2, 3] vs [1, 2, 3]
//     let v1_t1 = [1, 2, 3];
//     let v2_t1 = [1, 2, 3];
//     eq_vec_Int(&v1_t1, 3, &v2_t1, 3);

//     // Test case 2: Different lengths (3 vs 2)
//     let v1_t2 = [1, 2, 3];
//     let v2_t2 = [1, 2];
//     eq_vec_Int(&v1_t2, 3, &v2_t2, 2);

//     // Test case 3: Same length, different values [1, 2, 3] vs [1, 5, 3]
//     let v1_t3 = [1, 2, 3];
//     let v2_t3 = [1, 5, 3];
//     eq_vec_Int(&v1_t3, 3, &v2_t3, 3);

//     // Test case 4: Single element boundary [42] vs [42]
//     let v1_t4 = [42];
//     let v2_t4 = [42];
//     eq_vec_Int(&v1_t4, 1, &v2_t4, 1);

//     // Test case 5: Boundary with Max/Min Integers
//     let v1_t5 = [i32::MAX, i32::MIN];
//     let v2_t5 = [i32::MAX, i32::MIN];
//     eq_vec_Int(&v1_t5, 2, &v2_t5, 2);

//     // Test case 6: Empty arrays (Size 0)
//     let v1_t6: [i32; 0] = [];
//     let v2_t6: [i32; 0] = [];
//     eq_vec_Int(&v1_t6, 0, &v2_t6, 0);

//     // Test case 7: Mismatch on the last element
//     let v1_t7 = [10, 20, 30];
//     let v2_t7 = [10, 20, 31];
//     eq_vec_Int(&v1_t7, 3, &v2_t7, 3);
// }