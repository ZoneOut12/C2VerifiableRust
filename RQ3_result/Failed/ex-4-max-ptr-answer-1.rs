use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::math::*;
use vstd::slice::*;
verus! {

extern "C" {
    
exec static mut h: i32;

}


#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]

fn max_ptr(a: &i32, b: &i32) -> (result: i32)
requires
	true&&true,
ensures
	(((a)@)<((b)@)) as int != 0 ==> (result==((b)@)) as int != 0,
	(((a)@)>=((b)@)) as int != 0 ==> (result==((a)@)) as int != 0,
	result==((a)@)||result==((b)@),
 {
    if *a < *b { *b } else { *a }
}




#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]

fn main() {
    unsafe { h = 42; }
    let a: i32 = 24;
    let b: i32 = 42;
    let x: i32 = max_ptr(&a, &b);
    assert(x==42);
    assert(h==42);
}
} // verus!
