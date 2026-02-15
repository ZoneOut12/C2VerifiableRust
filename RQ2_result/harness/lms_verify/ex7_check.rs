// #[allow(unused_imports)]
// use vstd::math::*;
// use vstd::prelude::*;
// use vstd::slice::*;
// verus! {

// #[verifier::external_body]
// #[verifier::loop_isolation(false)]
// #[verifier::exec_allows_no_decreases_clause]
// fn member(x0: &[i32], x1: i32, x2: i32) -> (result: i32)
//     requires
//         ((x1 > 0) && x0@.len() >= x1 - 1 + 1),
//     ensures
//         ((((result == -1)) as int != 0 ==> ((!(((exists|x56: i32|
//             (((0 <= x56) && (x56 < x1)) && (x0@[(x56) as int] == x2)))) as int != 0))) as int != 0)
//             && (((result != -1)) as int != 0 ==> ((((0 <= result) && (result < x1)) && (x0@[(
//         result) as int] == x2))) as int != 0)),
// {
//     let mut x4: i32 = -1;
//     let mut x6: i32 = 0;
//     while x6 < x1
//         invariant
//             ((((0 <= x6) && (x6 <= x1)) && (((x4 == -1)) as int != 0 ==> ((!(((exists|x22: i32|
//                 (((0 <= x22) && (x22 < x6)) && (x0@[(x22) as int] == x2)))) as int != 0))) as int
//                 != 0)) && (((x4 != -1)) as int != 0 ==> ((((0 <= x4) && (x4 < x6)) && (x0@[(
//             x4) as int] == x2))) as int != 0)),
//         decreases (x1 - x6),
//     {
//         let x7: i32 = x4;
//         let x8: i32 = if x7 == -1 {
//             1
//         } else {
//             0
//         };
//         let x11: i32;
//         if x8 != 0 {
//             let x9: i32 = x0[x6 as usize];
//             let x10: i32 = if x9 == x2 {
//                 1
//             } else {
//                 0
//             };
//             x11 = x10;
//         } else {
//             x11 = 0;
//         }
//         if x11 != 0 {
//             x4 = x6;
//         }
//         x6 += 1;
//     }
//     let x50: i32 = x4;
//     x50
// }

// fn CheckPre_member(x0: &[i32], x1: i32, x2: i32)
//     requires
//         ((x1 > 0) && x0@.len() >= x1 - 1 + 1),
// {}

// fn CheckPost_member(x0: &[i32], x1: i32, x2: i32, result: i32)
//     requires
//         ((((result == -1)) as int != 0 ==> ((!(((exists|x56: i32|
//             (((0 <= x56) && (x56 < x1)) && (x0@[(x56) as int] == x2)))) as int != 0))) as int != 0)
//             && (((result != -1)) as int != 0 ==> ((((0 <= result) && (result < x1)) && (x0@[(
//         result) as int] == x2))) as int != 0)),
// {}

// fn main() {
// }

// fn valid_test_harness() {
//     // Test case 1: Element found in middle
//     let arr1 = [1, 2, 3, 4];
//     CheckPre_member(&arr1, 4, 3);
//     CheckPost_member(&arr1, 4, 3, 2);

//     // Test case 2: Element not found
//     let arr2 = [5, 6, 7];
//     CheckPre_member(&arr2, 3, 4);
//     CheckPost_member(&arr2, 3, 4, -1);

//     // Test case 3: Element at first position
//     let arr3 = [10, 20, 30];
//     CheckPre_member(&arr3, 3, 10);
//     CheckPost_member(&arr3, 3, 10, 0);

//     // Test case 4: Element at last position
//     let arr4 = [10, 20, 30];
//     CheckPre_member(&arr4, 3, 30);
//     CheckPost_member(&arr4, 3, 30, 2);

//     // Test case 5: Single element match
//     let arr5 = [42];
//     CheckPre_member(&arr5, 1, 42);
//     CheckPost_member(&arr5, 1, 42, 0);

//     // Test case 8: Boundary - single element no match
//     let arr8 = [5];
//     CheckPre_member(&arr8, 1, 6);
//     CheckPost_member(&arr8, 1, 6, -1);

//     // Test case 9: Boundary - two elements match at last
//     let arr9 = [0, 1];
//     CheckPre_member(&arr9, 2, 1);
//     CheckPost_member(&arr9, 2, 1, 1);
// }

// fn invalid_test_harness() {
//     // Test case 6: Invalid - size x1 equals zero
//     let arr6 = [1, 2, 3];
//     CheckPre_member(&arr6, 0, 1);

//     // Test case 7: Invalid - null pointer equivalent
//     let arr7: [i32; 0] = [];
//     CheckPre_member(&arr7, 3, 1);
// }

// } // verus!

// RAC
fn member(x0: &[i32], x1: i32, x2: i32) -> i32
{
    let mut x4: i32 = -1;
    let mut x6: i32 = 0;
    while x6 < x1
    {
        let old_measure = x1 - x6;
        assert!(
            ((0 <= x6) && (x6 <= x1)) && (!(x4 == -1) || (!(0..x6).any(|x22| (x0[(x22) as usize] == x2)))) && (!(x4 != -1) || ((((0 <= x4) && (x4 < x6)) && (x0[(
            x4) as usize] == x2)))),
        );
        let x7: i32 = x4;
        let x8: i32 = if x7 == -1 {
            1
        } else {
            0
        };
        let x11: i32;
        if x8 != 0 {
            let x9: i32 = x0[x6 as usize];
            let x10: i32 = if x9 == x2 {
                1
            } else {
                0
            };
            x11 = x10;
        } else {
            x11 = 0;
        }
        if x11 != 0 {
            x4 = x6;
        }
        x6 += 1;
        assert!(old_measure > x1 - x6);
    }
    assert!(
        ((0 <= x6) && (x6 <= x1)) && (!(x4 == -1) || (!(0..x6).any(|x22| (x0[(x22) as usize] == x2)))) && (!(x4 != -1) || ((((0 <= x4) && (x4 < x6)) && (x0[(
        x4) as usize] == x2)))),
    );
    let x50: i32 = x4;
    x50
}

fn main() {
    valid_test_harness();    
}

fn valid_test_harness() {
    // Test case 1: Element found in middle
    let arr1 = [1, 2, 3, 4];
    member(&arr1, 4, 3);

    // Test case 2: Element not found
    let arr2 = [5, 6, 7];
    member(&arr2, 3, 4);

    // Test case 3: Element at first position
    let arr3 = [10, 20, 30];
    member(&arr3, 3, 10);

    // Test case 4: Element at last position
    let arr4 = [10, 20, 30];
    member(&arr4, 3, 30);

    // Test case 5: Single element match
    let arr5 = [42];
    member(&arr5, 1, 42);

    // Test case 8: Boundary - single element no match
    let arr8 = [5];
    member(&arr8, 1, 6);

    // Test case 9: Boundary - two elements match at last
    let arr9 = [0, 1];
    member(&arr9, 2, 1);
}