#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub uninterp spec fn gcd(a: int, b: int) -> int;

#[verifier::external_body]
pub broadcast proof fn nil()
    ensures
        forall|n: int| (gcd(n as int, 0 as int)) == n,
{
}

#[verifier::external_body]
pub broadcast proof fn next()
    ensures
        forall|a: int, b: int| (gcd(b as int, a % b as int)) == (gcd(a as int, b as int)),
{
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn gcd(a: u32, b: u32) -> (result: u32)
    ensures
        result == (gcd(a as int, b as int)),
    decreases b,
{
    broadcast use nil, next;

    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

fn main() {
}

} // verus!
