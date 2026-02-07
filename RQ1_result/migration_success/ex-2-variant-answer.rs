#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo() {
    let mut x: i32 = -20;

    while x < 0
        decreases -x,
    {
        x += 4;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn bar() {
    let mut x: i32 = -20;
    let mut i: i32 = 5;

    while x < 0
        invariant
            (-i) * 4 == x,
        decreases i,
    {
        x += 4;
        i -= 1;
    }
}

fn main() {
}

} // verus!
