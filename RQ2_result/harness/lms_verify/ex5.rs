#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn array_swap(p: &mut [i32])
    requires
        old(p)@.len() >= 1 + 1,
    ensures
        p@[(0) as int] == old(p)@[(1) as int],
        p@[(1) as int] == old(p)@[(0) as int],
{
    let tmp: i32 = p[0];
    p[0] = p[1];
    p[1] = tmp;
}

fn CheckPre_array_swap(p: &[i32])
    requires
        p@.len() >= 1 + 1,
{}

fn CheckPost_array_swap(p: &[i32], old_p: &[i32])
    requires
        p@[(0) as int] == old_p@[(1) as int],
        p@[(1) as int] == old_p@[(0) as int],
{}

fn main() {
}

fn valid_test_harness() {
    // Test case 1: Normal array [1, 2]
    let mut arr1 = [1, 2];
    CheckPre_array_swap(&arr1);
    let result1 = [2, 1];
    CheckPost_array_swap(&result1, &arr1);

    // Test case 2: Negative and zero values [-5, 0]
    let mut arr2 = [-5, 0];
    CheckPre_array_swap(&arr2);
    let result2 = [0, -5];
    CheckPost_array_swap(&result2, &arr2);

    // Test case 3: Identical elements [42, 42]
    let mut arr3 = [42, 42];
    CheckPre_array_swap(&arr3);
    let result3 = [42, 42];
    CheckPost_array_swap(&result3, &arr3);

    // Test case 4: Large values [1000, 2000]
    let mut arr4 = [1000, 2000];
    CheckPre_array_swap(&arr4);
    let result4 = [2000, 1000];
    CheckPost_array_swap(&result4, &arr4);

    // Test case 5: Zero and positive value [0, 5]
    let mut arr5 = [0, 5];
    CheckPre_array_swap(&arr5);
    let result5 = [5, 0];
    CheckPost_array_swap(&result5, &arr5);

    // Test case 8: Boundary - minimal valid size [0, 1]
    let mut arr8 = [0, 1];
    CheckPre_array_swap(&arr8);
    let result8 = [1, 0];
    CheckPost_array_swap(&result8, &arr8);

    // Test case 9: Array with extra elements [10, 20, 30]
    let mut arr9 = [10, 20, 30];
    CheckPre_array_swap(&arr9);
    let result9 = [20, 10, 30];
    CheckPost_array_swap(&result9, &arr9);
}

fn invalid_test_harness(){
    let mut arr1 = [];
    CheckPre_array_swap(&arr1);
    
    let mut arr2 = [5];
    CheckPre_array_swap(&arr2); 
}

} // verus!