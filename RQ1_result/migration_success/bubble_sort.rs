#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn bubbleSort(a: &mut [i32], n: i32)
    requires
        old(a)@.len() >= n - 1 + 1,
        n > 0,
    ensures
        forall|i: int, j: int|
            (0 <= i <= j <= n - 1) as int != 0 ==> (a@[(i) as int] <= a@[(j) as int]) as int != 0,
{
    let mut i: i32;
    let mut j: i32;

    i = n - 1;
    while i > 0
        invariant
            forall|p: int, q: int|
                (i <= p <= q <= n - 1) as int != 0 ==> (a@[(p) as int] <= a@[(q) as int]) as int
                    != 0,
            forall|p: int, q: int|
                (0 <= p < i + 1 == q <= n - 1) as int != 0 ==> (a@[(p) as int] <= a@[(
                q) as int]) as int != 0,
            0 <= i < n,
        decreases i,
    {
        j = 0;
        while j < i
            invariant
                0 <= j <= i < n,
                forall|k: int|
                    (0 <= k <= j) as int != 0 ==> (a@[(k) as int] <= a@[(j) as int]) as int != 0,
                forall|p: int, q: int|
                    (0 <= p < i + 1 == q <= n - 1) as int != 0 ==> (a@[(p) as int] <= a@[(
                    q) as int]) as int != 0,
            decreases i - j,
        {
            if a[j as usize] > a[(j + 1) as usize] {
                let temp: i32 = a[j as usize];
                a[j as usize] = a[(j + 1) as usize];
                a[(j + 1) as usize] = temp;
            }
            j += 1;
        }
        i -= 1;
    }
}

fn main() {
}

} // verus!
