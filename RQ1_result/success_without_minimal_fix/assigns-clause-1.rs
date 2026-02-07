#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

const x: i32 = 0;

#[verifier::external_body]
fn ghost_foo() {
    unimplemented!();
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo() {
    let mut i: i32 = 0;
    while i < 10 {
        i += 1;
    }
}

fn main() {
}

} // verus!
