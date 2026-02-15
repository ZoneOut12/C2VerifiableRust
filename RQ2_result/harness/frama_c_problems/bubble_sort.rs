#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

fn CheckPre_bubbleSort(old_a: &[i32], n: i32)
    requires
        old_a@.len() >= n - 1 + 1,
        n > 0,
{}

fn CheckPost_bubbleSort(a: &[i32], n: i32)
    requires
        forall|i: int, j: int|
            (0 <= i <= j <= n - 1) as int != 0 ==> (a@[(i) as int] <= a@[(j) as int]) as int != 0,
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn bubbleSort(a: &mut [i32], n: i32)
    requires
        old(a)@.len() >= n - 1 + 1,
        n > 0,
    ensures
        forall|i: int, j: int|
            (0 <= i <= j <= n - 1) as int != 0 ==> (a@[(i) as int] <= a@[(j) as int]) as int != 0,
{
    let mut i: i32;
    let mut j: i32;

    i = n - 1;
    while i > 0
        invariant
            forall|k: int, p: int| (i + 1) < k <= n - 1 && 0 <= p <= k ==> (a@[(p) as int]) <= a@[(k) as int], //2A
            (a)@.len() >= n - 1 + 1, //2C
            forall|p: int, q: int|
                (i <= p <= q <= n - 1) as int != 0 ==> (a@[(p) as int] <= a@[(q) as int]) as int
                    != 0,
            forall|p: int, q: int|
                (0 <= p < i + 1 == q <= n - 1) as int != 0 ==> (a@[(p) as int] <= a@[(
                q) as int]) as int != 0,
            0 <= i < n,
        decreases i,
    {
        j = 0;
        while j < i
            invariant
                forall|k: int, p: int| (i + 1) < k <= n - 1 && 0 <= p <= k ==> (a@[(p) as int]) <= a@[(k) as int], //2A
                (a)@.len() >= n - 1 + 1, //2C
                0 <= j <= i < n,
                forall|k: int|
                    (0 <= k <= j) as int != 0 ==> (a@[(k) as int] <= a@[(j) as int]) as int != 0,
                forall|p: int, q: int|
                    (0 <= p < i + 1 == q <= n - 1) as int != 0 ==> (a@[(p) as int] <= a@[(
                    q) as int]) as int != 0,
            decreases i - j,
        {
            if a[j as usize] > a[(j + 1) as usize] {
                let temp: i32 = a[j as usize];
                a[j as usize] = a[(j + 1) as usize];
                a[(j + 1) as usize] = temp;
            }
            j += 1;
        }
        i -= 1;
    }
}

fn main() {
}

fn valid_test_harness_bubbleSort() {
    // Test case 1: Valid - normal array
    let arr1 = [3, 1, 4, 1, 5];
    CheckPre_bubbleSort(&arr1, 5);
    let result1 = [1, 1, 3, 4, 5];
    CheckPost_bubbleSort(&result1, 5);

    // Test case 2: Valid - already sorted array
    let arr2 = [1, 2, 3, 4];
    CheckPre_bubbleSort(&arr2, 4);
    let result2 = [1, 2, 3, 4];
    CheckPost_bubbleSort(&result2, 4);

    // Test case 3: Valid - reverse sorted array
    let arr3 = [5, 4, 3];
    CheckPre_bubbleSort(&arr3, 3);
    let result3 = [3, 4, 5];
    CheckPost_bubbleSort(&result3, 3);

    // Test case 4: Valid - array with duplicates
    let arr4 = [2, 2, 1];
    CheckPre_bubbleSort(&arr4, 3);
    let result4 = [1, 2, 2];
    CheckPost_bubbleSort(&result4, 3);

    // Test case 5: Valid - minimal valid size (n=2)
    let arr5 = [5, 3];
    CheckPre_bubbleSort(&arr5, 2);
    let result5 = [3, 5];
    CheckPost_bubbleSort(&result5, 2);

    // Test case 6: Boundary - minimal size (n=1)
    let arr6 = [42];
    CheckPre_bubbleSort(&arr6, 1);
    let result6 = [42];
    CheckPost_bubbleSort(&result6, 1);

    // Test case 7: Boundary - equal elements
    let arr7 = [7, 7];
    CheckPre_bubbleSort(&arr7, 2);
    let result7 = [7, 7];
    CheckPost_bubbleSort(&result7, 2);
}

fn invalid_test_harness_bubbleSort() {
    // Test case 8: Invalid - n=0 violates n > 0
    let arr8 = [1, 2, 3];
    CheckPre_bubbleSort(&arr8, 0);

    // Test case 9: Invalid - NULL equivalent (None)
    CheckPre_bubbleSort(&[], 3);
}

} // verus!


// RAC
// fn bubbleSort(a: &mut [i32], n: i32)
// {
//     let mut i: i32;
//     let mut j: i32;

//     i = n - 1;
//     while i > 0
//         // invariant
//         //     forall|k: int, p: int| (i + 1) < k <= n - 1 && 0 <= p <= k ==> (a@[(p) as int]) <= a@[(k) as int], //2A
//         //     (a)@.len() >= n - 1 + 1, //2C
//         //     forall|p: int, q: int|
//         //         (i <= p <= q <= n - 1) as int != 0 ==> (a@[(p) as int] <= a@[(q) as int]) as int
//         //             != 0,
//         //     forall|p: int, q: int|
//         //         (0 <= p < i + 1 == q <= n - 1) as int != 0 ==> (a@[(p) as int] <= a@[(
//         //         q) as int]) as int != 0,
//         //     0 <= i < n,
//         // decreases i,
//     {
//         let old_measure = i;
//         assert!(
//             ((i + 2)..n).all(|k| {
//                 (0..=k).all(|p| {
//                     (a[(p) as usize]) <= a[(k) as usize]
//                 })
//             }) &&
//             a.len() as i32 >= n - 1 + 1 &&
//             (i..n).all(|p| {
//                 (p..n).all(|q| {
//                     a[(p) as usize] <= a[(q) as usize]
//                 })
//             }) &&
//             (0..i+1).all(|p| 
//                 ((i+1)..n).all(|q| a[(p) as usize] <= a[(q) as usize])
//             ) &&
//             0 <= i && i < n,
//         );
//         j = 0;
//         while j < i
//             // invariant
//             //     forall|k: int, p: int| (i + 1) < k <= n - 1 && 0 <= p <= k ==> (a@[(p) as int]) <= a@[(k) as int], //2A
//             //     (a)@.len() >= n - 1 + 1, //2C
//             //     0 <= j <= i < n,
//             //     forall|k: int|
//             //         (0 <= k <= j) as int != 0 ==> (a@[(k) as int] <= a@[(j) as int]) as int != 0,
//             //     forall|p: int, q: int|
//             //         (0 <= p < i + 1 == q <= n - 1) as int != 0 ==> (a@[(p) as int] <= a@[(
//             //         q) as int]) as int != 0,
//             // decreases i - j,
//         {
//             let old_measure2 = i - j;
//             assert!(
//                 ((i + 2)..n).all(|k| {
//                     (0..=k).all(|p| {
//                         a[(p) as usize] <= a[(k) as usize]
//                     })
//                 }) && 
//                 (a).len() as i32 >= n - 1 + 1 &&
//                 0 <= j && j <= i && i < n &&
//                 (0..=j).all(|k| a[(k) as usize] <= a[(j) as usize]) &&
//                 (0..(i+1)).all(|p| 
//                     ((i+1)..n).all(|q| a[(p) as usize] <= a[(q) as usize])
//                 ) 
//             );
//             if a[j as usize] > a[(j + 1) as usize] {
//                 let temp: i32 = a[j as usize];
//                 a[j as usize] = a[(j + 1) as usize];
//                 a[(j + 1) as usize] = temp;
//             }
//             j += 1;
//             assert!(old_measure2 > i - j);
//         }
//         assert!(
//             ((i + 2)..n).all(|k| {
//                 (0..=k).all(|p| {
//                     a[(p) as usize] <= a[(k) as usize]
//                 })
//             }) && 
//             (a).len() as i32 >= n - 1 + 1 &&
//             0 <= j && j <= i && i < n &&
//             (0..=j).all(|k| a[(k) as usize] <= a[(j) as usize]) &&
//             (0..(i+1)).all(|p| 
//                 ((i+1)..n).all(|q| a[(p) as usize] <= a[(q) as usize])
//             ) 
//         );
//         i -= 1;
//         assert!(old_measure > i);
//     }
//     assert!(
//         ((i + 2)..n).all(|k| {
//             (0..=k).all(|p| {
//                 (a[(p) as usize]) <= a[(k) as usize]
//             })
//         }) &&
//         a.len() as i32 >= n - 1 + 1 &&
//         (i..n).all(|p|
//             (p..n).all(|q|
//                 a[(p) as usize] <= a[(q) as usize]
//             )
//         ) &&
//         (0..i+1).all(|p| 
//             ((i+1)..n).all(|q| a[(p) as usize] <= a[(q) as usize])
//         ) &&
//         0 <= i && i < n,
//     );
// }

// fn main() {
//     valid_test_harness_bubbleSort();
// }

// fn valid_test_harness_bubbleSort() {
//     // Test case 1: Valid - normal array
//     let mut arr1 = [3, 1, 4, 1, 5];
//     bubbleSort(&mut arr1, 5);

//     // Test case 2: Valid - already sorted array
//     let mut arr2 = [1, 2, 3, 4];
//     bubbleSort(&mut arr2, 4);

//     // Test case 3: Valid - reverse sorted array
//     let mut arr3 = [5, 4, 3];
//     bubbleSort(&mut arr3, 3);

//     // Test case 4: Valid - array with duplicates
//     let mut arr4 = [2, 2, 1];
//     bubbleSort(&mut arr4, 3);

//     // Test case 5: Valid - minimal valid size (n=2)
//     let mut arr5 = [5, 3];
//     bubbleSort(&mut arr5, 2);

//     // Test case 6: Boundary - minimal size (n=1)
//     let mut arr6 = [42];
//     bubbleSort(&mut arr6, 1);

//     // Test case 7: Boundary - equal elements
//     let mut arr7 = [7, 7];
//     bubbleSort(&mut arr7, 2);
// }
