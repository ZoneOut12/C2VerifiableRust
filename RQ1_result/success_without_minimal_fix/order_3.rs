#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn min3(x: int, y: int, z: int) -> int {
    if (x <= y && x <= z) {
        x
    } else {
        (if y <= z {
            y
        } else {
            z
        })
    }
}

pub open spec fn max3(x: int, y: int, z: int) -> int {
    if (x >= y && x >= z) {
        x
    } else {
        (if y >= z {
            y
        } else {
            z
        })
    }
}

pub open spec fn mid3(x: int, y: int, z: int) -> int {
    x + y + z - (min3(x as int, y as int, z as int)) - (max3(x as int, y as int, z as int))
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn order_3(a: &mut i32, b: &mut i32, c: &mut i32)
    requires
        true && true && true,
        true,
    ensures
        ((a)@) <= ((b)@) <= ((c)@),
        (((old(a))@) == ((old(b))@) == ((old(c))@)) as int != 0 ==> ((((a)@) == ((b)@) == ((
        c)@))) as int != 0,
        ((a)@) == (min3(((old(a))@) as int, ((old(b))@) as int, ((old(c))@) as int)),
        ((b)@) == (mid3(((old(a))@) as int, ((old(b))@) as int, ((old(c))@) as int)),
        ((c)@) == (max3(((old(a))@) as int, ((old(b))@) as int, ((old(c))@) as int)),
{
    if *a > *b {
        let temp: i32 = *a;
        *a = *b;
        *b = temp;
    }
    if *a > *c {
        let temp: i32 = *a;
        *a = *c;
        *c = temp;
    }
    if *b > *c {
        let temp: i32 = *b;
        *b = *c;
        *c = temp;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn test() {
    let mut a1: i32 = 5;
    let mut b1: i32 = 3;
    let mut c1: i32 = 4;
    order_3(&mut a1, &mut b1, &mut c1);
    assert(a1 == 3 && b1 == 4 && c1 == 5);

    let mut a2: i32 = 2;
    let mut b2: i32 = 2;
    let mut c2: i32 = 2;
    order_3(&mut a2, &mut b2, &mut c2);
    assert(a2 == 2 && b2 == 2 && c2 == 2);

    let mut a3: i32 = 4;
    let mut b3: i32 = 3;
    let mut c3: i32 = 4;
    order_3(&mut a3, &mut b3, &mut c3);
    assert(a3 == 3 && b3 == 4 && c3 == 4);

    let mut a4: i32 = 4;
    let mut b4: i32 = 5;
    let mut c4: i32 = 4;
    order_3(&mut a4, &mut b4, &mut c4);
    assert(a4 == 4 && b4 == 4 && c4 == 5);
}

fn main() {
}

} // verus!
