#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn index_where_even(x0: &[i32], x1: i32, x2: &mut [i32]) -> (result: i32)
    requires
        (((x1 > 0) && x0@.len() >= x1 - 1 + 1) && old(x2)@.len() >= x1 - 1 + 1),
    ensures
        ((((0 <= result) && (result <= x1)) && (forall|x74: i32|
            ((((0 <= x74) && (x74 < result))) as int != 0 ==> (((0 <= x2@[(x74) as int]) && (x2@[(
            x74) as int] < x1))) as int != 0))) && (forall|x86: i32|
            ((((0 < x86) && (x86 < result))) as int != 0 ==> ((x2@[((x86 - 1)) as int] < x2@[(
            x86) as int])) as int != 0))),
{
    let mut x5: i32 = 0;
    let mut x6: i32 = 0;
    while x6 < x1
        invariant
            ((((((0 <= x6) && (x6 <= x1)) && (0 <= x5)) && (x5 <= x6)) && (forall|x28: i32|
                ((((0 <= x28) && (x28 < x5))) as int != 0 ==> (((0 <= x2@[(x28) as int]) && (x2@[(
                x28) as int] < x6))) as int != 0))) && (forall|x42: i32|
                ((((0 < x42) && (x42 < x5))) as int != 0 ==> ((x2@[((x42 - 1)) as int] < x2@[(
                x42) as int])) as int != 0))),
        decreases (x1 - x6),
    {
        let x7: i32 = x0[x6 as usize];
        let x8: i32 = x7 % 2;
        let x9: bool = x8 == 0;
        if x9 {
            let x10: i32 = x5;
            x2[x10 as usize] = x6;
            x5 += 1;
        }
        x6 += 1;
    }
    let x62: i32 = x5;
    x62
}

fn main() {
}

} // verus!
