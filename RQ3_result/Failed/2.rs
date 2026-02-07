#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn sum(n: char) -> (result: i32)
    requires
        n >= 0 && n <= 100,
    ensures
        result >= 0,
        result == (n + 1) * (n) / 2,
{
    let mut s: i32 = 0;
    let mut k: char = 0 as char;
    while k <= n
        invariant
            0 <= k <= n + 1,
            s == (k - 1) * (k) / 2,
        decreases n - k,
    {
        s = s + k as i32;
        k = char::from_u32(k as u32 + 1).unwrap();
    }
    s
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let s: i32 = sum(5 as char);
    assert(s == 15);
}

} // verus!
