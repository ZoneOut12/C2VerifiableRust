use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::math::*;
use vstd::slice::*;
verus! {

extern "C" {
    
exec static mut old: i32;

    
exec static mut new: i32;

}


#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]

fn abs(x: i32) -> (result: i32)
requires
	x>i32::MIN,
ensures
	(x>=0) as int != 0 ==> (result==x) as int != 0,
	(x<0) as int != 0 ==> (result==-x) as int != 0,
 {
    if x >= 0 {
        x
    } else {
        -x
    }
}




#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]

fn distance(a: i32, b: i32) -> (result: i32)
requires
	i32::MIN<b-a<=i32::MAX,
ensures
	(a<b) as int != 0 ==> (a+result==b) as int != 0,
	(b<=a) as int != 0 ==> (a-result==b) as int != 0,
 {
    abs(b - a)
}




#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]

fn old_distance(a: i32, b: i32) -> (result: i32)
requires
	(a<b) as int != 0 ==> (b-a<=i32::MAX) as int != 0,
	(b<=a) as int != 0 ==> (a-b<=i32::MAX) as int != 0,
ensures
	(a<b) as int != 0 ==> (a+result==b) as int != 0,
	(b<=a) as int != 0 ==> (a-result==b) as int != 0,
 {
    if a < b {
        b - a
    } else {
        a - b
    }
}




#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]

fn test(a: i32, b: i32)
requires
	i32::MIN<b-a<=i32::MAX,
 {
    unsafe {
        old = old_distance(a, b);
        new = distance(a, b);
    }
    assert(old==new);
}


fn main(){}
} // verus!
