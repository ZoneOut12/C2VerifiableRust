verus! {

pub mod libmath {
    #[allow(unused_imports)]


    use vstd::math::*;
    use vstd::prelude::*;
    #[allow(unused_imports)]
    use vstd::slice::*;

    #[verifier::external_fn_specification]
    pub fn i32_abs(x: i32) -> (result: i32)
        ensures
            result >= 0,
            result == if x < 0 {
                -x as int
            } else {
                x as int
            },
    {
        x.abs()
    }

}

} // verus!
#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::slice::*;

verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn my_abs(x: i32) -> (result: i32)
    requires
        x > i32::MIN,
    ensures
        result >= 0,
{
    x.abs()
}

fn main() {
}

} // verus!
