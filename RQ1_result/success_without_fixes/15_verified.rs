#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::external_body]
fn unknown() -> (result: i32) {
    unimplemented!();
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(n: i32)
    requires
        n > 0,
{
    let mut x: i32 = 0;
    let mut m: i32 = 0;

    while x < n
        invariant
            x <= n,
            (n > 0) as int != 0 ==> (m >= 0) as int != 0,
            (n > 0) as int != 0 ==> (m < n) as int != 0,
            m <= x,
            0 <= x,
        decreases n - x,
    {
        if unknown() != 0 {
            m = x;
        }
        x = x + 1;
    }

    if n > 0 {
        assert(m < n);
        assert(m >= 0);
    }
}

fn main() {
}

} // verus!
