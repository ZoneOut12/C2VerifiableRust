#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

fn CheckPre_inswap(old_x0: &[i32], x1: i32, x2: i32)
    requires
        ((old_x0)@.len() - x1 >= 1 && (old_x0)@.len() - x2 >= 1),
{}

fn CheckPost_inswap(old_x0: &[i32], x0: &[i32], x1: i32, x2: i32)
    requires 
        ((x0@[(x1) as int] == old_x0@[(x2) as int]) && (x0@[(x2) as int] == old_x0@[(
        x1) as int])),
{}

#[verifier::external_body]
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn inswap(x0: &mut [i32], x1: i32, x2: i32)
    requires
        ((old(x0))@.len() - x1 >= 1 && (old(x0))@.len() - x2 >= 1),
    ensures
        ((x0@[(x1) as int] == old(x0)@[(x2) as int]) && (x0@[(x2) as int] == old(x0)@[(
        x1) as int])),
{
    let x4: i32 = x0[x1 as usize];
    let x5: i32 = x0[x2 as usize];
    x0[x1 as usize] = x5;
    x0[x2 as usize] = x4;
}

fn CheckPre_insort(old_x22: &[i32], x23: i32)
    requires
        ((x23 > 0) && old_x22@.len() >= x23 - 1 + 1),
{}

fn CheckPost_insort(x22: &[i32], x23: i32)
    requires
        (forall|x174: i32|
        ((((0 <= x174) && (x174 < (x23 - 1)))) as int != 0 ==> ((x22@[(x174) as int] <= x22@[(#[trigger](
        x174 + 1)) as int])) as int != 0)),
{}

#[verifier::external_body]
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn insort(x22: &mut [i32], x23: i32)
    requires
        ((x23 > 0) && old(x22)@.len() >= x23 - 1 + 1),
    ensures
        (forall|x174: i32|
            ((((0 <= x174) && (x174 < (x23 - 1)))) as int != 0 ==> ((x22@[(x174) as int] <= x22@[(#[trigger](
            x174 + 1)) as int])) as int != 0)),
{
    let mut x26: i32 = x23;
    while true
        invariant
            ((((0 <= x26) && (x26 <= x23)) && (forall|x130: i32|
                ((((x26 <= x130) && (x130 < (x23 - 1)))) as int != 0 ==> ((x22@[(x130) as int]
                    <= x22@[((x130 + 1)) as int])) as int != 0))) && (forall|x143: i32|
                (((((0 <= x143) && (x143 < x26)) && (x26 <= (x23 - 1)))) as int != 0 ==> ((x22@[(
                x143) as int] <= x22@[(x26) as int])) as int != 0))),
        decreases x26,
    {
        let x27: i32 = x26;
        let x28: bool = x27 > 1;
        if !x28 {
            break ;
        }
        let mut x30: i32 = 0;
        let x31: i32 = x26;
        let mut x33: i32 = 0;
        while x33 < x31
            invariant
                ((((((((0 <= x26) && (x26 <= x23)) && (0 <= x33)) && (x33 <= x26)) && (0 <= x30))
                    && (x30 <= (x26 - 1))) && ((x26 - 1) < x23)) && (forall|x62: i32|
                    ((((0 <= x62) && (x62 < x33))) as int != 0 ==> ((x22@[(x62) as int] <= x22@[(
                    x30) as int])) as int != 0))),
            decreases (x26 - x33),
        {
            let x34: i32 = x22[x33 as usize];
            let x35: i32 = x30;
            let x36: i32 = x22[x35 as usize];
            let x37: bool = x34 >= x36;
            if x37 {
                x30 = x33;
            } else {
            }
            x33 += 1;
        }
        let x82: i32 = x30;
        let x81: i32 = x31 - 1;
        inswap(x22, x81, x82);
        assert((forall|x84: i32|
            (((((x26 - 1) < x84) && (x84 < (x23 - 1)))) as int != 0 ==> ((x22@[(x84) as int]
                <= x22@[((x84 + 1)) as int])) as int != 0)));
        assert((((x26 <= (x23 - 1))) as int != 0 ==> ((x22@[((x26 - 1)) as int] <= x22@[(
        x26) as int])) as int != 0));
        assert((forall|x108: i32|
            ((((0 <= x108) && (x108 < x26))) as int != 0 ==> ((x22@[(x108) as int] <= x22@[((x26
                - 1)) as int])) as int != 0)));
        x26 = x81;
    }
}

fn main() {
}

fn valid_test_harness_inswap() {
    // --- Test Case 1: Standard swap of different indices ---
    let mut arr1 = [10, 20, 30];
    CheckPre_inswap(&arr1, 0, 2);
    // After logic: [30, 20, 10]
    let res1 = [30, 20, 10];
    CheckPost_inswap(&[10, 20, 30], &res1, 0, 2);

    // --- Test Case 2: Swapping adjacent elements ---
    let mut arr2 = [1, 2, 3];
    CheckPre_inswap(&arr2, 0, 1);
    let res2 = [2, 1, 3];
    CheckPost_inswap(&[1, 2, 3], &res2, 0, 1);

    // --- Test Case 3: Identity swap (x1 == x2) ---
    // ACSL contract allows x1 == x2; ensures x0[x1] == old(x0[x1])
    let mut arr3 = [100, 200];
    CheckPre_inswap(&arr3, 1, 1);
    let res3 = [100, 200];
    CheckPost_inswap(&[100, 200], &res3, 1, 1);

    // --- Test Case 4: Negative values in array ---
    let mut arr4 = [-5, 0, 5];
    CheckPre_inswap(&arr4, 0, 2);
    let res4 = [5, 0, -5];
    CheckPost_inswap(&[-5, 0, 5], &res4, 0, 2);

    // --- Test Case 5: Large array (Heap allocated) ---
    let mut arr5 = [0; 100];
    arr5[0] = 1; arr5[99] = 99;
    CheckPre_inswap(&arr5, 0, 99);
    let mut updated_arr5 = [0; 100];
    updated_arr5[0] = 99;
    updated_arr5[99] = 1;
    // logic: swap 1 and 99
    CheckPost_inswap(&arr5, &updated_arr5, 0, 99);

    // --- Test Case 6: Boundary - last elements ---
    let mut arr6 = [10, 20, 30, 40];
    CheckPre_inswap(&arr6, 2, 3);
    let res6 = [10, 20, 40, 30];
    CheckPost_inswap(&[10, 20, 30, 40], &res6, 2, 3);

    // --- Test Case 7: Extreme values (INT_MIN/MAX) ---
    let mut arr7 = [i32::MIN, i32::MAX];
    CheckPre_inswap(&arr7, 0, 1);
    let res7 = [i32::MAX, i32::MIN];
    CheckPost_inswap(&[i32::MIN, i32::MAX], &res7, 0, 1);
}

fn invalid_test_harness_inswap() {
    let mut arr = [1, 2, 3];

    // --- Test Case 8: Invalid - Offset x1 out of bounds ---
    // x0 + 10 is not a valid pointer for an array of size 3
    // let (x1_bad, x2_ok) = (10, 0);
    // CheckPre_inswap(&arr, x1_bad, x2_ok);

    // --- Test Case 9: Invalid - Base pointer is NULL ---
    // x0 is NULL, so x0 + x1 can never be \valid
    // unsafe {
    //     let null_ptr: *mut i32 = std::ptr::null_mut();
    //     // Simulating the passing of a null base address to the checker
    //     // This violates \valid(x0 + x1)
    //     CheckPre_inswap(null_ptr, 0, 1);
    // }
}

fn valid_test_harness_insort() {
    // --- Test Case 1: Normal unsorted array ---
    let mut arr1 = [3, 1, 4, 1, 5];
    CheckPre_insort(&arr1, 5);
    // Logic: result should be [1, 1, 3, 4, 5]
    let res1 = [1, 1, 3, 4, 5];
    CheckPost_insort(&res1, 5);

    // --- Test Case 2: Already sorted array ---
    let mut arr2 = [1, 2, 3, 4, 5];
    CheckPre_insort(&arr2, 5);
    let res2 = [1, 2, 3, 4, 5];
    CheckPost_insort(&res2, 5);

    // --- Test Case 3: All elements equal ---
    let mut arr3 = [5, 5, 5, 5];
    CheckPre_insort(&arr3, 4);
    let res3 = [5, 5, 5, 5];
    CheckPost_insort(&res3, 4);

    // --- Test Case 4: Reverse-sorted 2-element array ---
    let mut arr4 = [2, 1];
    CheckPre_insort(&arr4, 2);
    let res4 = [1, 2];
    CheckPost_insort(&res4, 2);

    // --- Test Case 5: Reverse-sorted 3-element array ---
    let mut arr5 = [5, 3, 1];
    CheckPre_insort(&arr5, 3);
    let res5 = [1, 3, 5];
    CheckPost_insort(&res5, 3);

    // --- Test Case 8: Boundary - Size 1 ---
    let mut arr8 = [42];
    CheckPre_insort(&arr8, 1);
    let res8 = [42];
    CheckPost_insort(&res8, 1);

    // --- Test Case 9: Boundary - Two equal elements ---
    let mut arr9 = [2, 2];
    CheckPre_insort(&arr9, 2);
    let res9 = [2, 2];
    CheckPost_insort(&res9, 2);
}

fn invalid_test_harness_insort() {
    // // --- Test Case 6: Invalid - Size zero ---
    // // Violates: requires x23 > 0
    // let mut arr6 = [1, 2, 3];
    // CheckPre_insort(arr6.as_mut_ptr(), 0);

    // // --- Test Case 7: Invalid - NULL pointer ---
    // // Violates: requires \valid(x22+(0..x23-1))
    // unsafe {
    //     let null_ptr: *mut i32 = std::ptr::null_mut();
    //     CheckPre_insort(null_ptr, 3);
    // }
}

} // verus!

// RAC
// fn inswap(x0: &mut [i32], x1: i32, x2: i32)
// {
//     let x4: i32 = x0[x1 as usize];
//     let x5: i32 = x0[x2 as usize];
//     x0[x1 as usize] = x5;
//     x0[x2 as usize] = x4;
// }

// fn insort(x22: &mut [i32], x23: i32)
// {
//     let mut x26: i32 = x23;
//     while true
//     {
//         let old_measure = x26;
//         assert!(
//                 (((0 <= x26) && (x26 <= x23)) && 
//                 (x26..(x23 - 1)).all(|x130| (x22[(x130) as usize]
//                     <= x22[((x130 + 1)) as usize]))
//                 ) && ((0..x26).all(|x143: i32| !(x26 <= (x23 - 1)) || (x22[(
//                 x143) as usize] <= x22[(x26) as usize])))
//         );
//         let x27: i32 = x26;
//         let x28: bool = x27 > 1;
//         if !x28 {
//             break ;
//         }
//         let mut x30: i32 = 0;
//         let x31: i32 = x26;
//         let mut x33: i32 = 0;
//         while x33 < x31
//         {
//             let old_measure2 = (x26 - x33);
//             assert!(
//                     ((((((((0 <= x26) && (x26 <= x23)) && (0 <= x33)) && (x33 <= x26)) && (0 <= x30))
//                     && (x30 <= (x26 - 1))) && ((x26 - 1) < x23)) && (
//                         (0..x33).all(|x62| (x22[(x62) as usize] <= x22[(x30) as usize]))
//                 ))
//             );
//             let x34: i32 = x22[x33 as usize];
//             let x35: i32 = x30;
//             let x36: i32 = x22[x35 as usize];
//             let x37: bool = x34 >= x36;
//             if x37 {
//                 x30 = x33;
//             } else {
//             }
//             x33 += 1;
//             assert!(old_measure2 > (x26 - x33));
//         }
//         assert!(
//             ((((((((0 <= x26) && (x26 <= x23)) && (0 <= x33)) && (x33 <= x26)) && (0 <= x30))
//             && (x30 <= (x26 - 1))) && ((x26 - 1) < x23)) && (
//                 (0..x33).all(|x62| (x22[(x62) as usize] <= x22[(x30) as usize]))
//             ))
//         );
//         let x82: i32 = x30;
//         let x81: i32 = x31 - 1;
//         inswap(x22, x81, x82);
//         assert!((x26..(x23 - 1)).all(|x84| (x22[(x84) as usize]
//                 <= x22[((x84 + 1)) as usize])));
//         assert!((!((x26 <= (x23 - 1))) || ((x22[((x26 - 1)) as usize] <= x22[(
//         x26) as usize]))));
//         assert!((0..x26).all(|x108: i32| (x22[(x108) as usize] <= x22[((x26
//                 - 1)) as usize])));
//         x26 = x81;
//         assert!(old_measure > x26);
//     }
//     assert!(
//         (((0 <= x26) && (x26 <= x23)) && 
//         (x26..(x23 - 1)).all(|x130| (x22[(x130) as usize]
//             <= x22[((x130 + 1)) as usize]))
//         ) && ((0..x26).all(|x143: i32| !(x26 <= (x23 - 1)) || (x22[(
//         x143) as usize] <= x22[(x26) as usize])))
//     );
// }

// fn main() {
//     valid_test_harness_insort();
// }

// fn valid_test_harness_insort() {
//     // --- Test Case 1: Normal unsorted array ---
//     let mut arr1 = [3, 1, 4, 1, 5];
//     insort(&mut arr1, 5);

//     // --- Test Case 2: Already sorted array ---
//     let mut arr2 = [1, 2, 3, 4, 5];
//     insort(&mut arr2, 5);

//     // --- Test Case 3: All elements equal ---
//     let mut arr3 = [5, 5, 5, 5];
//     insort(&mut arr3, 4);

//     // --- Test Case 4: Reverse-sorted 2-element array ---
//     let mut arr4 = [2, 1];
//     insort(&mut arr4, 2);

//     // --- Test Case 5: Reverse-sorted 3-element array ---
//     let mut arr5 = [5, 3, 1];
//     insort(&mut arr5, 3);

//     // --- Test Case 8: Boundary - Size 1 ---
//     let mut arr8 = [42];
//     insort(&mut arr8, 1);

//     // --- Test Case 9: Boundary - Two equal elements ---
//     let mut arr9 = [2, 2];
//     insort(&mut arr9, 2);
// }