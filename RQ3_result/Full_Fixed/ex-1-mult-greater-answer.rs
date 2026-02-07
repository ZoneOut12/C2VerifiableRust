#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {


pub open spec fn assist(x: int, y: int, z: int) -> bool { x >= 0 } //2a

pub proof fn mult_greater()
    ensures
        forall|x: int, y: int, z: int|
            #[trigger] assist(x, y, z) as int != 0 ==> ((y <= z) as int != 0 ==> (x * y <= x * z) as int != 0) as int//2b
                != 0,
{
}

fn main() {
}

} // verus!
