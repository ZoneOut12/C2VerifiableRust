#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(n: i32, m: i32, l: i32) -> (result: i32)
    requires
        i32::MIN < 3 * n < i32::MAX,
        i32::MIN < m && m < i32::MAX,
        i32::MIN < l && l < i32::MAX,
        i32::MIN < m + l < i32::MAX,
{
    if 3 * n <= m + l {
        let mut i: i32 = 0;
        while i < n
            invariant
                0 <= i,
            decreases n - i,
        {
            let mut j: i32 = 2 * i;
            while j < 3 * i
                invariant
                    i <= n,
                    2 * i <= j,
                    0 <= i,
                decreases 3 * i - j,
            {
                let mut k: i32 = i;
                while k < j
                    decreases j - k,
                {
                    assert(k - i <= 2 * n);
                    k += 1;
                }
                j += 1;
            }
            i += 1;
        }
    }
    0
}

fn main() {
}

} // verus!
