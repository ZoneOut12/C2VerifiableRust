#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn inc(x0: i32) -> (result: i32)
    requires
        (x0 < i32::MAX),
    ensures
        (result > x0),
{
    let x2: i32 = x0 + 1;
    x2
}

fn CheckPost_inc(x0: i32, result: i32)
    requires
        (result > x0),
{}

fn main() {
}

fn valid_test_harness(){
    inc(0);
    let result = 1;
    CheckPost_inc(0, result);

    inc(42);
    let result = 43;
    CheckPost_inc(42, result);

    inc(-10);
    let result = -9;
    CheckPost_inc(-10, result);

    inc(1000);
    let result = 1001;
    CheckPost_inc(1000, result);

    inc(i32::MAX - 100);
    let result = i32::MAX - 99;
    CheckPost_inc(i32::MAX - 100, result);

    inc(i32::MAX - 1);
    let result = i32::MAX;
    CheckPost_inc(i32::MAX - 1, result);
}

fn invalid_test_harness(){
    inc(i32::MAX);
}

} // verus!
