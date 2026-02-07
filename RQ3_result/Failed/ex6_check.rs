#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn inswap(x0: &mut [i32], x1: i32, x2: i32)
    requires
        ((old(x0) + x1)@.len() >= 1 && (old(x0) + x2)@.len() >= 1),
    ensures
        ((x0@[(x1) as int] == old(x0)@[(x2) as int]) && (x0@[(x2) as int] == old(x0)@[(
        x1) as int])),
{
    let x4: i32 = x0[x1 as usize];
    let x5: i32 = x0[x2 as usize];
    x0[x1 as usize] = x5;
    x0[x2 as usize] = x4;
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn insort(x22: &mut [i32], x23: i32)
    requires
        ((x23 > 0) && old(x22)@.len() >= x23 - 1 + 1),
    ensures
        (forall|x174: i32|
            ((((0 <= x174) && (x174 < (x23 - 1)))) as int != 0 ==> ((x22@[(x174) as int] <= x22@[((
            x174 + 1)) as int])) as int != 0)),
{
    let mut x26: i32 = x23;
    while true
        invariant
            ((((0 <= x26) && (x26 <= x23)) && (forall|x130: i32|
                ((((x26 <= x130) && (x130 < (x23 - 1)))) as int != 0 ==> ((x22@[(x130) as int]
                    <= x22@[((x130 + 1)) as int])) as int != 0))) && (forall|x143: i32|
                (((((0 <= x143) && (x143 < x26)) && (x26 <= (x23 - 1)))) as int != 0 ==> ((x22@[(
                x143) as int] <= x22@[(x26) as int])) as int != 0))),
        decreases x26,
    {
        let x27: i32 = x26;
        let x28: bool = x27 > 1;
        if !x28 {
            break ;
        }
        let mut x30: i32 = 0;
        let x31: i32 = x26;
        let mut x33: i32 = 0;
        while x33 < x31
            invariant
                ((((((((0 <= x26) && (x26 <= x23)) && (0 <= x33)) && (x33 <= x26)) && (0 <= x30))
                    && (x30 <= (x26 - 1))) && ((x26 - 1) < x23)) && (forall|x62: i32|
                    ((((0 <= x62) && (x62 < x33))) as int != 0 ==> ((x22@[(x62) as int] <= x22@[(
                    x30) as int])) as int != 0))),
            decreases (x26 - x33),
        {
            let x34: i32 = x22[x33 as usize];
            let x35: i32 = x30;
            let x36: i32 = x22[x35 as usize];
            let x37: bool = x34 >= x36;
            if x37 {
                x30 = x33;
            } else {
            }
            x33 += 1;
        }
        let x82: i32 = x30;
        let x81: i32 = x31 - 1;
        inswap(x22, x81, x82);
        assert((forall|x84: i32|
            (((((x26 - 1) < x84) && (x84 < (x23 - 1)))) as int != 0 ==> ((x22@[(x84) as int]
                <= x22@[((x84 + 1)) as int])) as int != 0)));
        assert((((x26 <= (x23 - 1))) as int != 0 ==> ((x22@[((x26 - 1)) as int] <= x22@[(
        x26) as int])) as int != 0));
        assert((forall|x108: i32|
            ((((0 <= x108) && (x108 < x26))) as int != 0 ==> ((x22@[(x108) as int] <= x22@[((x26
                - 1)) as int])) as int != 0)));
        x26 = x81;
    }
}

fn main() {
}

} // verus!
