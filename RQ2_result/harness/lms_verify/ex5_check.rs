#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_swap(x0: &mut [i32])
    requires
        old(x0)@.len() >= 1 + 1,
    ensures
        ((x0@[(0) as int] == old(x0)@[(1) as int]) && (x0@[(1) as int] == old(x0)@[(0) as int])),
{
    let x2: i32 = x0[0];
    let x3: i32 = x0[1];
    x0[0] = x3;
    x0[1] = x2;
}

fn CheckPre_array_swap(x0: &[i32])
    requires 
        (x0)@.len() >= 1 + 1,
{} 

fn CheckPost_array_swap(x0: &[i32], old_x0: &[i32])
    requires 
        ((x0@[(0) as int] == old_x0@[(1) as int]) && (x0@[(1) as int] == old_x0@[(0) as int])),
{}

fn main() {
}

fn valid_test_harness() {
    // Test case 1: Normal swap [1, 2]
    let mut arr1 = [1, 2];
    CheckPre_array_swap(&arr1);
    let result1 = [2, 1];
    CheckPost_array_swap(&result1, &arr1);

    // Test case 2: Equal values [5, 5]
    let mut arr2 = [5, 5];
    CheckPre_array_swap(&arr2);
    let result2 = [5, 5];
    CheckPost_array_swap(&result2, &arr2);

    // Test case 3: Negative numbers [-3, -7]
    let mut arr3 = [-3, -7];
    CheckPre_array_swap(&arr3);
    let result3 = [-7, -3];
    CheckPost_array_swap(&result3, &arr3);

    // Test case 4: Zero and positive [0, 42]
    let mut arr4 = [0, 42];
    CheckPre_array_swap(&arr4);
    let result4 = [42, 0];
    CheckPost_array_swap(&result4, &arr4);

    // Test case 5: Zero and negative [0, -1]
    let mut arr5 = [0, -1];
    CheckPre_array_swap(&arr5);
    let result5 = [-1, 0];
    CheckPost_array_swap(&result5, &arr5);

    // Test case 6: Max and min integers
    let mut arr6 = [i32::MAX, i32::MIN];
    CheckPre_array_swap(&arr6);
    let result6 = [i32::MIN, i32::MAX];
    CheckPost_array_swap(&result6, &arr6);

    // Test case 7: Adjacent values [1, 0]
    let mut arr7 = [1, 0];
    CheckPre_array_swap(&arr7);
    let result7 = [0, 1];
    CheckPost_array_swap(&result7, &arr7);
}

fn invalid_test_harness() {
    // In Rust, references cannot be null. An empty slice is the closest safe equivalent.
    let arr8: [i32; 0] = [];
    CheckPre_array_swap(&arr8);

    // Test case 9: Insufficient array size [5]
    let arr9 = [3];
    CheckPre_array_swap(&arr9);
}

} // verus!