#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn factorial(n: int) -> int {
    if (n <= 0) {
        1
    } else {
        n * (factorial(n - 1 as int))
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn facto(n: i32) -> (result: i32)
    requires
        n <= 12,
    ensures
        result == (factorial(n as int)),
{
    if n < 2 {
        return 1;
    }
    let mut res: i32 = 1;
    let mut i: i32 = 2;
    while i <= n
        invariant
            2 <= i <= n + 1,
            res == (factorial(i - 1 as int)),
        decreases n - i,
    {
        res = res * i;
        i += 1;
    }
    res
}

fn main() {
}

} // verus!
