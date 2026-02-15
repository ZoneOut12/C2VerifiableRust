// #[allow(unused_imports)]
// use vstd::math::*;
// use vstd::prelude::*;
// use vstd::slice::*;
// verus! {

// #[verifier::loop_isolation(false)]
// #[verifier::exec_allows_no_decreases_clause]
// fn arraymax(a: &[i32], n: i32) -> (result: i32)
//     requires
//         a@.len() >= n - 1 + 1,
//         n > 0,
//     ensures
//         forall|k: int| (0 <= k < n) as int != 0 ==> (result >= a@[(k) as int]) as int != 0,
//         exists|k: int| 0 <= k < n && result == a@[(k) as int],
// {
//     let mut i: i32 = 1;
//     let mut max: i32 = a[0];

//     while i < n
//         invariant
//             exists|k: int| 0 <= k < i && max == a@[(k) as int],
//             forall|k: int| (0 <= k < i) as int != 0 ==> (max >= a@[(k) as int]) as int != 0,
//             0 <= i <= n,
//         decreases n - i,
//     {
//         if max < a[i as usize] {
//             max = a[i as usize];
//             assert(exists|k: int| 0 <= k < i + 1 && max == a@[(k) as int]);
//         }
//         i = i + 1;
//     }
//     max
// }

// fn CheckPre_arraymax(a: &[i32], n: i32)
//     requires
//         a@.len() >= n - 1 + 1,
//         n > 0,
// {}

// fn CheckPost_arraymax(a: &[i32], n: i32, result: i32)
//     requires
//         forall|k: int| (0 <= k < n) as int != 0 ==> (result >= a@[(k) as int]) as int != 0,
//         exists|k: int| 0 <= k < n && result == a@[(k) as int],
// {}

// fn main() {
// }

// fn valid_test_harness_arraymax() {
//     // Test case 1: Valid - normal increasing array
//     let arr1 = [1, 2, 3, 4, 5];
//     let n1 = 5;
//     CheckPre_arraymax(&arr1, n1);
//     let result1 = 5;
//     CheckPost_arraymax(&arr1, n1, result1);

//     // Test case 2: Valid - normal decreasing array
//     let arr2 = [5, 4, 3, 2, 1];
//     let n2 = 5;
//     CheckPre_arraymax(&arr2, n2);
//     let result2 = 5;
//     CheckPost_arraymax(&arr2, n2, result2);

//     // Test case 3: Valid - mixed array with max in middle
//     let arr3 = [3, 1, 4, 2];
//     let n3 = 4;
//     CheckPre_arraymax(&arr3, n3);
//     let result3 = 4;
//     CheckPost_arraymax(&arr3, n3, result3);

//     // Test case 4: Valid - all elements same
//     let arr4 = [2, 2, 2];
//     let n4 = 3;
//     CheckPre_arraymax(&arr4, n4);
//     let result4 = 2;
//     CheckPost_arraymax(&arr4, n4, result4);

//     // Test case 5: Valid - single element array
//     let arr5 = [42];
//     let n5 = 1;
//     CheckPre_arraymax(&arr5, n5);
//     let result5 = 42;
//     CheckPost_arraymax(&arr5, n5, result5);

//     // Test case 6: Boundary - all elements same (n=2)
//     let arr6 = [9, 9];
//     let n6 = 2;
//     CheckPre_arraymax(&arr6, n6);
//     let result6 = 9;
//     CheckPost_arraymax(&arr6, n6, result6);

//     // Test case 7: Boundary - two elements with max first
//     let arr7 = [7, 3];
//     let n7 = 2;
//     CheckPre_arraymax(&arr7, n7);
//     let result7 = 7;
//     CheckPost_arraymax(&arr7, n7, result7);
// }

// fn invalid_test_harness_arraymax() {
//     // Test case 8: Invalid - n=0 violates n > 0
//     let arr8 = [1, 2, 3];
//     CheckPre_arraymax(&arr8, 0);

//     // Test case 9: Invalid - NULL array pointer simulation
//     CheckPre_arraymax(None, 3);
// }

// } // verus!


// RAC
fn arraymax(a: &[i32], n: i32) -> i32
{
    let mut i: i32 = 1;
    let mut max: i32 = a[0];

    while i < n
    {
        let old_measure = n - i;
        assert!(
            (0..i).any(|k| max == a[(k) as usize]) && 
            (0..i).all(|k| max >= a[(k) as usize]) &&
            0 <= i && i <= n
        );
        if max < a[i as usize] {
            max = a[i as usize];
            assert!((0..i+1).any(|k| max == a[(k) as usize]));
        }
        i = i + 1;
        assert!(old_measure > n - i);
    }
    assert!(
        (0..i).any(|k| max == a[(k) as usize]) && 
        (0..i).all(|k| max >= a[(k) as usize]) &&
        0 <= i && i <= n
    );
    max
}

fn main() {
    valid_test_harness_arraymax();
}

fn valid_test_harness_arraymax() {
    // Test case 1: Valid - normal increasing array
    let arr1 = [1, 2, 3, 4, 5];
    let n1 = 5;
    arraymax(&arr1, n1);

    // Test case 2: Valid - normal decreasing array
    let arr2 = [5, 4, 3, 2, 1];
    let n2 = 5;
    arraymax(&arr2, n2);

    // Test case 3: Valid - mixed array with max in middle
    let arr3 = [3, 1, 4, 2];
    let n3 = 4;
    arraymax(&arr3, n3);

    // Test case 4: Valid - all elements same
    let arr4 = [2, 2, 2];
    let n4 = 3;
    arraymax(&arr4, n4);

    // Test case 5: Valid - single element array
    let arr5 = [42];
    let n5 = 1;
    arraymax(&arr5, n5);

    // Test case 6: Boundary - all elements same (n=2)
    let arr6 = [9, 9];
    let n6 = 2;
    arraymax(&arr6, n6);

    // Test case 7: Boundary - two elements with max first
    let arr7 = [7, 3];
    let n7 = 2;
    arraymax(&arr7, n7);
}