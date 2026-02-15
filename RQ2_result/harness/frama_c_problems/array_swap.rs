#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_swap(arr: &mut [i32], n: i32, n1: i32, n2: i32)
    requires
        n >= 0,
        0 <= n1 < n && 0 <= n2 < n,
        old(arr)@.len() >= n - 1 + 1,
    ensures
        (arr@[(n2) as int] == old(arr)@[(n1) as int]) && (arr@[(n2) as int] == old(arr)@[(
        n1) as int]),
{
    let temp = arr[n1 as usize];
    arr[n1 as usize] = arr[n2 as usize];
    arr[n2 as usize] = temp;
}

fn CheckPre_array_swap(old_arr: &[i32], n: i32, n1: i32, n2: i32)
    requires
        n >= 0,
        0 <= n1 < n && 0 <= n2 < n,
        old_arr@.len() >= n - 1 + 1,
{}

fn CheckPost_array_swap(old_arr: &[i32], arr: &[i32], n: i32, n1: i32, n2: i32)
    requires
        (arr@[(n2) as int] == old_arr@[(n1) as int]) && (arr@[(n2) as int] == old_arr@[(
        n1) as int]),
{}

fn main() {
}

fn valid_test_harness_array_swap() {
    // Test case 1: Normal swap [1, 2, 3] -> [2, 1, 3] at indices 0, 1
    let arr1 = [1, 2, 3];
    CheckPre_array_swap(&arr1, 3, 0, 1);
    let result1 = [2, 1, 3];
    CheckPost_array_swap(&arr1, &result1, 3, 0, 1);

    // Test case 2: Same indices [5, 6] -> [5, 6] at indices 1, 1
    let arr2 = [5, 6];
    CheckPre_array_swap(&arr2, 2, 1, 1);
    let result2 = [5, 6];
    CheckPost_array_swap(&arr2, &result2, 2, 1, 1);

    // Test case 3: Middle elements swap [10, 20, 30, 40] -> [10, 20, 40, 30]
    let arr3 = [10, 20, 30, 40];
    CheckPre_array_swap(&arr3, 4, 2, 3);
    let result3 = [10, 20, 40, 30];
    CheckPost_array_swap(&arr3, &result3, 4, 2, 3);

    // Test case 4: First and last swap [0, 1, 2, 3] -> [3, 1, 2, 0]
    let arr4 = [0, 1, 2, 3];
    CheckPre_array_swap(&arr4, 4, 0, 3);
    let result4 = [3, 1, 2, 0];
    CheckPost_array_swap(&arr4, &result4, 4, 0, 3);

    // Test case 5: Non-adjacent swap [5, 4, 3, 2, 1] -> [5, 4, 1, 2, 3]
    let arr5 = [5, 4, 3, 2, 1];
    CheckPre_array_swap(&arr5, 5, 2, 4);
    let result5 = [5, 4, 1, 2, 3];
    CheckPost_array_swap(&arr5, &result5, 5, 2, 4);

    // Test case 8: Boundary - single element [42] -> [42]
    let arr8 = [42];
    CheckPre_array_swap(&arr8, 1, 0, 0);
    let result8 = [42];
    CheckPost_array_swap(&arr8, &result8, 1, 0, 0);

    // Test case 9: Boundary - 2-element swap [1, 2] -> [2, 1]
    let arr9 = [1, 2];
    CheckPre_array_swap(&arr9, 2, 0, 1);
    let result9 = [2, 1];
    CheckPost_array_swap(&arr9, &result9, 2, 0, 1);
}

fn invalid_test_harness_array_swap() {
    // Test case 6
    let arr6 = [1, 2, 3];
    CheckPre_array_swap(&arr6, -1, 0, 1);

    // Test case 7
    CheckPre_array_swap(&[1, 2], 3, 2, 0);
}

} // verus!
