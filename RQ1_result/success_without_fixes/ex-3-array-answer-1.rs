#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(a: &[i32; 10])
    requires
        a@.len() >= 9 + 1,
    ensures
        forall|j: int| (0 <= j < 10) as int != 0 ==> (a@[(j) as int] == a@[(j) as int]) as int != 0,
{
    let mut g: [i32; 10] = [0;10];

    {
        let mut i: i32 = 0;
        while i < 10
            invariant
                0 <= i <= 10,
                forall|j: int|
                    (0 <= j < i) as int != 0 ==> (a@[(j) as int] == g@[(j) as int]) as int != 0,
            decreases 10 - i,
        {
            g[i as usize] = a[i as usize];
            i += 1;
        }
    }

    {
        let mut i: i32 = 0;
        while i < 10
            invariant
                0 <= i <= 10,
                forall|j: int|
                    (0 <= j < 10) as int != 0 ==> (a@[(j) as int] == g@[(j) as int]) as int != 0,
            decreases 10 - i,
        {
            i += 1;
        }
    }
}

fn main() {
}

} // verus!
