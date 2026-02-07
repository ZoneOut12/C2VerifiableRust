#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn add(x: i32, y: i32) -> (result: i32)
    requires
        x + y <= i32::MAX,
        x + y >= i32::MIN,
    ensures
        result == x + y,
{
    x + y
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo() {
    let a: i32 = add(1, 43);
}

fn main() {
}

} // verus!
