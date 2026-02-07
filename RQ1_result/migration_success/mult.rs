#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn mul(a: i32, b: i32) -> (result: i32)
    requires
        a >= 0 && b >= 0,
        a * b <= i32::MAX,
    ensures
        result == a * b,
{
    let mut x: i32 = a;
    let mut prod: i32 = 0;
    while x > 0
        invariant
            x >= 0,
            prod == (a - x) * b,
        decreases x,
    {
        assert(x >= 1 && prod == (a - x) * b);
        assert(prod <= a * b - b);
        prod = prod + b;
        x -= 1;
    }
    prod
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let pdt: i32 = mul(2, 5);
    assert(pdt == 10);
}

} // verus!
