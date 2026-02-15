#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn inv_vec_Int(x0: &[i32], x1: int) -> bool {
    ((x1 == 0) || ((x1 > 0) && x0@.len() >= x1 - 1 + 1))
}

fn CheckPre_count_pos(x15: &[i32], x16: i32)
    requires
        (inv_vec_Int(x15, x16 as int)),
{}

fn CheckPost_count_pos(x15: &[i32], x16: i32, result: i32)
    requires
        (inv_vec_Int(x15, x16 as int)),
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn count_pos(x15: &[i32], x16: i32) -> (result: i32)
    requires
        (inv_vec_Int(x15, x16 as int)),
    ensures
        (inv_vec_Int(x15, x16 as int)),
{
    let mut x18: i32 = 0;
    let mut x20: i32 = 0;
    while x20 < x16
        invariant
            0 <= x20 <= x16,
            ((0 <= x18) && (x18 <= x20)),
        decreases x16 - x20,
    {
        let x22: i32 = x18;
        let x21: i32 = x15[x20 as usize];
        let x26: bool = x21 > 0;
        let x27: i32;
        if x26 {
            x27 = 1;
        } else {
            x27 = 0;
        }
        let x28: i32 = x22 + x27;
        x18 = x28;
        x20 += 1;
    }
    let x32: i32 = x18;
    x32
}

fn main() {
}

fn valid_test_harness() {
    // Test case 1: Valid - normal case with mixed values
    let arr1 = [1, -2, 3, 0, 5];
    CheckPre_count_pos(&arr1, 5);
    let result1 = 3; // Hardcoded Expected
    CheckPost_count_pos(&arr1, 5, result1);

    // Test case 2: Valid - all zeros
    let arr2 = [0, 0, 0];
    CheckPre_count_pos(&arr2, 3);
    let result2 = 0;
    CheckPost_count_pos(&arr2, 3, result2);

    // Test case 3: Valid - all positive
    let arr3 = [2, 3, 4, 5];
    CheckPre_count_pos(&arr3, 4);
    let result3 = 4;
    CheckPost_count_pos(&arr3, 4, result3);

    // Test case 4: Valid - mix of zero, positive, negative
    let arr4 = [0, 1, -1, 2];
    CheckPre_count_pos(&arr4, 4);
    let result4 = 2;
    CheckPost_count_pos(&arr4, 4, result4);

    // Test case 5: Valid - empty array logic (n=0)
    let arr5: [i32; 0] = [];
    CheckPre_count_pos(&arr5, 0);
    let result5 = 0;
    CheckPost_count_pos(&arr5, 0, result5);

    // Test case 6: Boundary - single zero element
    let arr6 = [0];
    CheckPre_count_pos(&arr6, 1);
    let result6 = 0;
    CheckPost_count_pos(&arr6, 1, result6);

    // Test case 7: Boundary - single positive element
    let arr7 = [5];
    CheckPre_count_pos(&arr7, 1);
    let result7 = 1;
    CheckPost_count_pos(&arr7, 1, result7);
}

fn invalid_test_harness() {
    // Test case 8: Invalid - negative array size
    let arr8 = [1, 2, 3];
    // In Rust, size (n) would usually be usize, but if passed as i32:
    CheckPre_count_pos(&arr8, -3);

    // Test case 9: Invalid - NULL equivalent (Buffer too small)
    let arr9: [i32; 0] = [];
    CheckPre_count_pos(&arr9, 3);
}

} // verus!

// RAC

// fn count_pos(x15: &[i32], x16: i32) -> i32
// {
//     let mut x18: i32 = 0;
//     let mut x20: i32 = 0;
//     while x20 < x16
//     {
//         let old_measure = x16 - x20;
//         assert!(
//             0 <= x20 && x20 <= x16 &&
//             ((0 <= x18) && (x18 <= x20))
//         );
//         let x22: i32 = x18;
//         let x21: i32 = x15[x20 as usize];
//         let x26: bool = x21 > 0;
//         let x27: i32;
//         if x26 {
//             x27 = 1;
//         } else {
//             x27 = 0;
//         }
//         let x28: i32 = x22 + x27;
//         x18 = x28;
//         x20 += 1;
//         assert!(old_measure > x16 - x20);
//     }
//     assert!(
//         0 <= x20 && x20 <= x16 &&
//         ((0 <= x18) && (x18 <= x20))
//     );
//     let x32: i32 = x18;
//     x32
// }

// fn main() {
//     valid_test_harness();
// }

// fn valid_test_harness() {
//     // Test case 1: Valid - normal case with mixed values
//     let arr = [1, -2, 3, 0, 5];
//     count_pos(&arr, 5);

//     // Test case 2: Valid - all zeros
//     let arr = [0, 0, 0];
//     count_pos(&arr, 3);

//     // Test case 3: Valid - all positive
//     let arr = [2, 3, 4, 5];
//     count_pos(&arr, 4);

//     // Test case 4: Valid - mix of zero, positive, negative
//     let arr = [0, 1, -1, 2];
//     count_pos(&arr, 4);

//     // Test case 5: Valid - empty array logic (n=0)
//     let arr: [i32; 0] = [];
//     count_pos(&arr, 0);

//     // Test case 6: Boundary - single zero element
//     let arr = [0];
//     count_pos(&arr, 1);

//     // Test case 7: Boundary - single positive element
//     let arr = [5];
//     count_pos(&arr, 1);
// }
