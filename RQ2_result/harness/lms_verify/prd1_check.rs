#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn ghost_is_pos(x0: i32) -> bool {//1
    (x0 > 0)
}

pub open spec fn ghost_is_nat(x3: i32) -> bool {//1
    (x3 >= 0)
}

fn CheckPost_is_pos(x0: i32, result: i32)
    requires
        (result) as int != 0 <==> ((ghost_is_pos(x0 as i32))) as int != 0,//1
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_pos(x0: i32) -> (result: i32)
    ensures
        (result) as int != 0 <==> ((ghost_is_pos(x0 as i32))) as int != 0,//1
{
    let x2: i32 = (x0 > 0) as i32;
    x2
}

fn CheckPost_is_nat(x3: i32, result: i32)
    requires
        (result) as int != 0 <==> ((ghost_is_nat(x3 as i32))) as int != 0,//1
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn is_nat(x3: i32) -> (result: i32)
    ensures
        (result) as int != 0 <==> ((ghost_is_nat(x3 as i32))) as int != 0,//1
{
    let x5: i32 = (x3 >= 0) as i32;
    x5
}


fn CheckPre_minus1(x6: i32)
    requires
        (ghost_is_pos(x6 as i32)),//1
{}

fn CheckPost_minus1(x6: i32, result: i32)
    requires
        (ghost_is_nat(result as i32)),//1
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn minus1(x6: i32) -> (result: i32)
    requires
        (ghost_is_pos(x6 as i32)),//1
    ensures
        (ghost_is_nat(result as i32)),//1
{
    let x8: i32 = x6 - 1;
    x8
}

fn main() {
}

fn valid_test_harness() {
    // --- is_pos() Test Cases (7 Valid) ---
    
    // Case 1: Minimum positive
    let res_pos_1 = 1; // true
    CheckPost_is_pos(1, res_pos_1);

    // Case 2: Typical positive
    let res_pos_2 = 1;
    CheckPost_is_pos(100, res_pos_2);

    // Case 3: Maximum boundary
    let res_pos_3 = 1;
    CheckPost_is_pos(i32::MAX, res_pos_3);

    // Case 4: Zero (not positive)
    let res_pos_4 = 0; // false
    CheckPost_is_pos(0, res_pos_4);

    // Case 5: Negative boundary
    let res_pos_5 = 0;
    CheckPost_is_pos(-1, res_pos_5);

    // Case 6: Typical negative
    let res_pos_6 = 0;
    CheckPost_is_pos(-100, res_pos_6);

    // Case 7: Minimum boundary
    let res_pos_7 = 0;
    CheckPost_is_pos(i32::MIN, res_pos_7);


    // --- is_nat() Test Cases (7 Valid) ---
    
    // Case 1: Minimum natural number
    let res_nat_1 = 1; // true
    CheckPost_is_nat(0, res_nat_1);

    // Case 2: Positive integer
    let res_nat_2 = 1;
    CheckPost_is_nat(1, res_nat_2);

    // Case 3: Maximum boundary
    let res_nat_3 = 1;
    CheckPost_is_nat(i32::MAX, res_nat_3);

    // Case 4: Negative boundary
    let res_nat_4 = 0; // false
    CheckPost_is_nat(-1, res_nat_4);

    // Case 5: Typical negative
    let res_nat_5 = 0;
    CheckPost_is_nat(-50, res_nat_5);

    // Case 6: Minimum boundary
    let res_nat_6 = 0;
    CheckPost_is_nat(i32::MIN, res_nat_6);

    // Case 7: Arbitrary natural
    let res_nat_7 = 1;
    CheckPost_is_nat(42, res_nat_7);


    // --- minus1() Test Cases (7 Valid) ---
    

    // Case 1: Boundary 1 -> 0
    CheckPre_minus1(1);
    let res_m1_1 = 0;
    CheckPost_minus1(1, res_m1_1);

    // Case 2: Small positive
    CheckPre_minus1(2);
    let res_m1_2 = 1;
    CheckPost_minus1(2, res_m1_2);

    // Case 3: Decade
    CheckPre_minus1(10);
    let res_m1_3 = 9;
    CheckPost_minus1(10, res_m1_3);

    // Case 4: Century
    CheckPre_minus1(100);
    let res_m1_4 = 99;
    CheckPost_minus1(100, res_m1_4);

    // Case 5: Max boundary
    CheckPre_minus1(i32::MAX);
    let res_m1_5 = i32::MAX - 1;
    CheckPost_minus1(i32::MAX, res_m1_5);

    // Case 6: Mid-range
    CheckPre_minus1(50);
    let res_m1_6 = 49;
    CheckPost_minus1(50, res_m1_6);

    // Case 7: Large positive
    CheckPre_minus1(999);
    let res_m1_7 = 998;
    CheckPost_minus1(999, res_m1_7);
}

fn invalid_test_harness() {
    // Case 8: Input 0 violates requires is_pos(x6)
    CheckPre_minus1(0);

    // Case 9: Input negative violates requires is_pos(x6)
    CheckPre_minus1(-5);
}

} // verus!
