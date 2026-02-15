#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn picker_first(x0: i32) -> (result: i32)
    requires
        (x0 > 0),
    ensures
        ((0 <= result) && (result < x0)),
{
    0
}

fn CheckPost_picker_first(x0: i32, result: i32)
    requires
        ((0 <= result) && (result < x0)),
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_first_element(x6: &[i32], x7: i32) -> (result: i32)
    requires
        ((x7 > 0) && x6@.len() >= x7 - 1 + 1),
{
    let x9: i32 = picker_first(x7);
    let x10: i32 = x6[x9 as usize];
    x10
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_first_directly(x15: &[i32], x16: i32) -> (result: i32)
    requires
        ((x16 > 0) && x15@.len() >= x16 - 1 + 1),
{
    let x18: i32 = x15[0];
    x18
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn picker_last(x23: i32) -> (result: i32)
    requires
        (x23 > 0),
    ensures
        ((0 <= result) && (result < x23)),
{
    let x25: i32 = x23 - 1;
    x25
}

fn CheckPost_picker_last(x23: i32, result: i32)
    requires
        ((0 <= result) && (result < x23)),
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_last_element(x30: &[i32], x31: i32) -> (result: i32)
    requires
        ((x31 > 0) && x30@.len() >= x31 - 1 + 1),
{
    let x33: i32 = picker_last(x31);
    let x34: i32 = x30[x33 as usize];
    x34
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pick_last_directly(x39: &[i32], x40: i32) -> (result: i32)
    requires
        ((x40 > 0) && x39@.len() >= x40 - 1 + 1),
{
    let x42: i32 = x40 - 1;
    let x43: i32 = x39[x42 as usize];
    x43
}

fn main() {
}

fn valid_test_harness() {
    // ---------- Case 1: n = 1 ----------
    let arr1 = [10];

    picker_first(1);
    let result = 0;
    CheckPost_picker_first(1, result);

    pick_first_element(&arr1, 1);

    pick_first_directly(&arr1, 1);

    picker_last(1);
    let result = 0;
    CheckPost_picker_last(1, result);

    pick_last_element(&arr1, 1);

    pick_last_directly(&arr1, 1);

    // ---------- Case 2: n = 3 ----------
    let arr2 = [1, 2, 3];

    picker_first(3);
    let result = 0;
    CheckPost_picker_first(3, result);

    pick_first_element(&arr2, 3);

    pick_first_directly(&arr2, 3);

    picker_last(3);
    let result = 2;
    CheckPost_picker_last(3, result);

    pick_last_element(&arr2, 3);

    pick_last_directly(&arr2, 3);

    // ---------- Case 3: negative values ----------
    let arr3 = [-5, -10, -15];

    picker_first(3);
    let result = 0;
    CheckPost_picker_first(3, result);

    pick_first_element(&arr3, 3);

    picker_last(3);
    let result = 2;
    CheckPost_picker_last(3, result);

    pick_last_element(&arr3, 3);

    // ---------- Case 4: mixed values ----------
    let arr4 = [0, -1, 42, -7];

    picker_first(4);
    let result = 0;
    CheckPost_picker_first(4, result);

    pick_first_directly(&arr4, 4);

    picker_last(4);
    let result = 3;
    CheckPost_picker_last(4, result);

    pick_last_directly(&arr4, 4);
}

fn invalid_test_harness(){
    let arr = [1, 2];
    picker_first(0);
    pick_first_element(&arr, 0);
    pick_first_directly(&arr, 0);
    picker_last(0);
    pick_last_element(&arr, 0);
    pick_last_directly(&arr, 0);

    let arr = [];
    picker_first(-1);
    pick_first_element(&arr, 1);
    pick_first_directly(&arr, 1);
    picker_last(-1);
    pick_last_element(&arr, 1);
    pick_last_directly(&arr, 1);
}

} // verus!
