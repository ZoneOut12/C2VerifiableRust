#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub uninterp spec fn is_gcd(a: int, b: int, d: int) -> bool;

#[verifier::external_body]
pub broadcast proof fn is_gcd_inductive()
    ensures
        forall|n: int| (is_gcd(n as int, 0 as int, n as int)),
        forall|a: int, b: int, d: int|
            ((is_gcd(b as int, a % b as int, d as int))) as int != 0 ==> (#[trigger](is_gcd(//2B
                a as int,
                b as int,
                d as int,
            ))) as int != 0,
{
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn gcd(a: u32, b: u32) -> (result: u32)
    requires
        a >= 0 && b >= 0,
    ensures
        (is_gcd(a as int, b as int, result as int)),
{
    broadcast use is_gcd_inductive;

    let a_pre: u32 = a;
    let b_pre: u32 = b;
    let mut a: u32 = a;
    let mut b: u32 = b;
    while b != 0
        invariant
            a >= 0 && b >= 0,
            forall|t: int|
                ((is_gcd(a as int, b as int, t as int))) as int != 0 ==> ((is_gcd(
                    a_pre as int,
                    b_pre as int,
                    t as int,
                ))) as int != 0,
        decreases b,
    {
        let t: u32 = b;
        b = a % b;
        a = t;
    }
    return a;
}

fn main() {
}

} // verus!
