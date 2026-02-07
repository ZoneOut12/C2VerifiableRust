#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub uninterp spec fn fact(n: int) -> int;

#[verifier::external_body]
pub broadcast proof fn case_n()
    ensures
        forall|n: int|
            (n >= 1) as int != 0 ==> ((fact(n as int)) == n * (#[trigger]fact(n - 1 as int))) as int != 0, //2B
{
}

#[verifier::external_body]
pub broadcast proof fn case_0()
    ensures
        (fact(0 as int)) == 1,
{
}

#[verifier::external_body]
pub broadcast proof fn monotonic()
    ensures
        forall|n: int|
            (n >= 0) as int != 0 ==> ((fact(n + 1 as int)) > #[trigger](fact(n as int))) as int != 0, //2B
{
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn factorial(n: i32) -> (result: i32)
    requires
        0 <= n < i32::MAX,
    ensures
        result == (fact(n as int)),
{
    broadcast use case_n, case_0, monotonic;

    let mut i: i32 = 1;
    let mut f: i32 = 1;

    while i <= n
        invariant
            f == (fact(i - 1 as int)),
            0 < i,
            i <= n + 1,
        decreases n + 1 - i,
    {
        f = f * i;
        i = i + 1;
    }
    f
}

fn main() {
}

} // verus!
