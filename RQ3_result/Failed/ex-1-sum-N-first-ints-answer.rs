#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub uninterp spec fn is_sum_n(n: int, res: int) -> bool;

#[verifier::external_body]
pub broadcast proof fn is_sum_n_inductive()
    ensures
        forall|n: int| (n <= 0) as int != 0 ==> ((is_sum_n(n as int, 0 as int))) as int != 0,
        forall|n: int, p: int|
            (n > 0) as int != 0 ==> (((is_sum_n(n - 1 as int, p as int))) as int != 0 ==> ((
            is_sum_n(n as int, n + p as int))) as int != 0) as int != 0,
{
}

#[verifier::external_body]
pub broadcast proof fn sum_n_value_direct()
    ensures
        forall|n: int, r: int|
            (n >= 0) as int != 0 ==> (((is_sum_n(n as int, r as int))) as int != 0 ==> (r == (n * (n
                + 1)) / 2) as int != 0) as int != 0,
{
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn sum_n(n: i32) -> (result: i32)
    requires
        n * (n + 1) <= 2 * i32::MAX,
    ensures
        (is_sum_n(n as int, result as int)),
{
    broadcast use is_sum_n_inductive, sum_n_value_direct;

    if n < 1 {
        return 0;
    }
    let mut res: i32 = 0;
    let mut i: i32 = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            (is_sum_n(i - 1 as int, res as int)),
        decreases n - i,
    {
        res += i;
        i += 1;
    }
    res
}

fn main() {
}

} // verus!
