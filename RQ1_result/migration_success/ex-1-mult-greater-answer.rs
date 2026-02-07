#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub proof fn mult_greater()
    ensures
        forall|x: int, y: int, z: int|
            (x >= 0) as int != 0 ==> ((y <= z) as int != 0 ==> (x * y <= x * z) as int != 0) as int
                != 0,
{
}

fn main() {
}

} // verus!
