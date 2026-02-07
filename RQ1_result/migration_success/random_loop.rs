#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::external_body]
fn random_between(min: usize, max: usize) -> (result: usize)
    ensures
        min <= result <= max,
{
    unimplemented!();
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn random_loop(bound: usize) {
    let mut i: usize = bound;
    while i > 0
        invariant
            0 <= i <= bound,
        decreases i,
    {
        i -= random_between(1, i);
    }
}

fn main() {
}

} // verus!
