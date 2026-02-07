#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max_ptr(a: &mut i32, b: &mut i32)
    requires
        true && true,
    ensures
        (((old(a))@) < ((old(b))@)) ==> (((a)@) == ((old(b))@) && ((b)@) == ((old(a))@)),
        (((old(a))@) >= ((old(b))@)) ==> (((a)@) == ((old(a))@) && ((b)@) == ((old(b))@)),
{
    if *a < *b {
        let tmp: i32 = *b;
        *b = *a;
        *a = tmp;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn min_ptr(a: &mut i32, b: &mut i32)
    requires
        true && true,
    ensures
        (((old(a))@) > ((old(b))@)) ==> (((a)@) == ((old(b))@) && ((b)@) == ((old(a))@)),
        (((old(a))@) <= ((old(b))@)) ==> (((a)@) == ((old(a))@) && ((b)@) == ((old(b))@)),
{
    max_ptr(b, a);
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn order_3_inc_max(a: &mut i32, b: &mut i32, c: &mut i32)
    requires
        true && true && true,
        true,
    ensures
        ((a)@) <= ((b)@) <= ((c)@),
        set!{((a)@),((b)@),((c)@)} == set!{((old(a))@),((old(b))@),((old(c))@)},
        (((old(a))@) == ((old(b))@) < ((old(c))@) || ((old(a))@) == ((old(c))@) < ((old(b))@) || ((
        old(b))@) == ((old(c))@) < ((old(a))@)) as int != 0 ==> (((a)@) == ((b)@)) as int != 0,
        (((old(a))@) == ((old(b))@) > ((old(c))@) || ((old(a))@) == ((old(c))@) > ((old(b))@) || ((
        old(b))@) == ((old(c))@) > ((old(a))@)) as int != 0 ==> (((b)@) == ((c)@)) as int != 0,
{
    max_ptr(c, b);
    max_ptr(c, a);
    max_ptr(b, a);
    assert (set!{((a)@),((b)@),((c)@)} == set!{((old(a))@),((old(b))@),((old(c))@)});//2A
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn order_3_inc_min(a: &mut i32, b: &mut i32, c: &mut i32)
    requires
        true && true && true,
        true,
    ensures
        ((a)@) <= ((b)@) <= ((c)@),
        set!{((a)@),((b)@),((c)@)} == set!{((old(a))@),((old(b))@),((old(c))@)},
        (((old(a))@) == ((old(b))@) < ((old(c))@) || ((old(a))@) == ((old(c))@) < ((old(b))@) || ((
        old(b))@) == ((old(c))@) < ((old(a))@)) as int != 0 ==> (((a)@) == ((b)@)) as int != 0,
        (((old(a))@) == ((old(b))@) > ((old(c))@) || ((old(a))@) == ((old(c))@) > ((old(b))@) || ((
        old(b))@) == ((old(c))@) > ((old(a))@)) as int != 0 ==> (((b)@) == ((c)@)) as int != 0,
{
    min_ptr(a, b);
    min_ptr(a, c);
    min_ptr(b, c);
    assert (set!{((a)@),((b)@),((c)@)} == set!{((old(a))@),((old(b))@),((old(c))@)});//2A
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn order_3_dec_max(a: &mut i32, b: &mut i32, c: &mut i32)
    requires
        true && true && true,
        true,
    ensures
        ((a)@) >= ((b)@) >= ((c)@),
        set!{((a)@),((b)@),((c)@)} == set!{((old(a))@),((old(b))@),((old(c))@)},
        (((old(a))@) == ((old(b))@) < ((old(c))@) || ((old(a))@) == ((old(c))@) < ((old(b))@) || ((
        old(b))@) == ((old(c))@) < ((old(a))@)) as int != 0 ==> (((b)@) == ((c)@)) as int != 0,
        (((old(a))@) == ((old(b))@) > ((old(c))@) || ((old(a))@) == ((old(c))@) > ((old(b))@) || ((
        old(b))@) == ((old(c))@) > ((old(a))@)) as int != 0 ==> (((a)@) == ((b)@)) as int != 0,
{
    max_ptr(a, b);
    max_ptr(a, c);
    max_ptr(b, c);
    assert (set!{((a)@),((b)@),((c)@)} == set!{((old(a))@),((old(b))@),((old(c))@)});//2A
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn order_3_dec_min(a: &mut i32, b: &mut i32, c: &mut i32)
    requires
        true && true && true,
        true,
    ensures
        ((a)@) >= ((b)@) >= ((c)@),
        set!{((a)@),((b)@),((c)@)} == set!{((old(a))@),((old(b))@),((old(c))@)},
        (((old(a))@) == ((old(b))@) < ((old(c))@) || ((old(a))@) == ((old(c))@) < ((old(b))@) || ((
        old(b))@) == ((old(c))@) < ((old(a))@)) as int != 0 ==> (((b)@) == ((c)@)) as int != 0,
        (((old(a))@) == ((old(b))@) > ((old(c))@) || ((old(a))@) == ((old(c))@) > ((old(b))@) || ((
        old(b))@) == ((old(c))@) > ((old(a))@)) as int != 0 ==> (((a)@) == ((b)@)) as int != 0,
{
    min_ptr(c, b);
    min_ptr(c, a);
    min_ptr(b, a);
    assert (set!{((a)@),((b)@),((c)@)} == set!{((old(a))@),((old(b))@),((old(c))@)});//2A
}

fn main() {
}

} // verus!
