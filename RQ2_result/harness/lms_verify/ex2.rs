#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_index(n: i32) -> (result: i32)
    requires
        n > 0,
    ensures
        0 <= result && result < n,
{
    0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_element(p: &[i32], n: i32) -> (result: i32)
    requires
        n > 0 && p@.len() >= n - 1 + 1,
{
    let i: i32 = pick_index(n);
    assert((0 <= i && i < n));
    p[i as usize]
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_first(p: &[i32]) -> (result: i32)
    requires
        (p)@.len() >= 1,
    ensures
        result == p@[(0) as int],
{
    p[0]
}

fn CheckPost_pick_first(p: &[i32], result: i32)
    requires
        result == p@[(0) as int],
{}

fn main() {
}

fn valid_test_harness_pick_element() {
    // Test case 1: n = 3, [1,2,3]
    let arr = [1, 2, 3];
    pick_element(&arr, 3);

    // Test case 2: single element
    let arr = [42];
    pick_element(&arr, 1);

    // Test case 3: zero and negative values
    let arr = [0, -5];
    pick_element(&arr, 2);

    // Test case 4: all negative
    let arr = [-1, -2, -3, -4];
    pick_element(&arr, 4);

    // Test case 5: larger array
    let arr = [10, 20, 30, 40, 50];
    pick_element(&arr, 5);

    // Test case 6: boundary n = 1
    let arr = [5];
    pick_element(&arr, 1);

    // Test case 7: exactly 2 elements
    let arr = [100, 200];
    pick_element(&arr, 2);
}

fn invalid_test_harness_pick_element() {
    let arr = [1, 2];
    pick_element(&arr, 0);

    let arr: &[i32] = &[];
    pick_element(arr, 2);
}

fn valid_test_harness_pick_first() {
    // Test case 1: single element
    let arr = [42];
    pick_first(&arr);
    let result = 42;
    CheckPost_pick_first(&arr, result);

    // Test case 2: multiple elements
    let arr = [1, 2, 3];
    pick_first(&arr);
    let result = 1;
    CheckPost_pick_first(&arr, result);

    // Test case 3: first element zero
    let arr = [0, 10, 20];
    pick_first(&arr);
    let result = 0;
    CheckPost_pick_first(&arr, result);

    // Test case 4: first element negative
    let arr = [-5, 3, 7];
    pick_first(&arr);
    let result = -5;
    CheckPost_pick_first(&arr, result);

    // Test case 5: larger array
    let arr = [100, 200, 300, 400];
    pick_first(&arr);
    let result = 100;
    CheckPost_pick_first(&arr, result);
}

fn invalid_test_harness_pick_first() {
    let arr: &[i32] = &[];
    pick_first(arr);
}

} // verus!

// RAC 
// fn pick_index(n: i32) -> i32
// {
//     0
// }

// fn pick_element(p: &[i32], n: i32) -> i32
// {
//     let i: i32 = pick_index(n);
//     assert!((0 <= i && i < n));
//     p[i as usize]
// }


// fn main() {
// }

// fn valid_test_harness_pick_element() {
//     // Test case 1: n = 3, [1,2,3]
//     let arr = [1, 2, 3];
//     pick_element(&arr, 3);

//     // Test case 2: single element
//     let arr = [42];
//     pick_element(&arr, 1);

//     // Test case 3: zero and negative values
//     let arr = [0, -5];
//     pick_element(&arr, 2);

//     // Test case 4: all negative
//     let arr = [-1, -2, -3, -4];
//     pick_element(&arr, 4);

//     // Test case 5: larger array
//     let arr = [10, 20, 30, 40, 50];
//     pick_element(&arr, 5);

//     // Test case 6: boundary n = 1
//     let arr = [5];
//     pick_element(&arr, 1);

//     // Test case 7: exactly 2 elements
//     let arr = [100, 200];
//     pick_element(&arr, 2);
// }