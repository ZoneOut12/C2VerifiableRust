#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn div_rem(x: u32, y: u32, q: &mut u32, r: &mut u32)
    requires
        true && true,
        true,
        y != 0,
    ensures
        x == ((q)@) * y + ((r)@),
        ((r)@) < y,
{
    *q = x / y;
    *r = x % y;
}

fn CheckPre_div_rem(x: u32, y: u32, old_q: &u32, old_r: &u32)
    requires
        y != 0,
{}

fn CheckPost_div_rem(x: u32, y: u32, q: &u32, r: &u32)
    requires
        x == ((q)@) * y + ((r)@),
        ((r)@) < y,
{}

fn main() {
}

fn valid_test_harness_div_rem() {
    // Test case 1: x=10, y=3 -> q=3, r=1
    let x1 = 10; let y1 = 3;
    let (q1, r1) = (3, 1);
    CheckPre_div_rem(x1, y1, &q1, &r1);
    CheckPost_div_rem(x1, y1, &q1, &r1);

    // Test case 2: x=5, y=5 -> q=1, r=0
    let x2 = 5; let y2 = 5;
    let (q2, r2) = (1, 0);
    CheckPre_div_rem(x2, y2, &q2, &r2);
    CheckPost_div_rem(x2, y2, &q2, &r2);

    // Test case 3: x=0, y=5 -> q=0, r=0
    let x3 = 0; let y3 = 5;
    let (q3, r3) = (0, 0);
    CheckPre_div_rem(x3, y3, &q3, &r3);
    CheckPost_div_rem(x3, y3, &q3, &r3);

    // Test case 4: x=1, y=1 -> q=1, r=0
    let x4 = 1; let y4 = 1;
    let (q4, r4) = (1, 0);
    CheckPre_div_rem(x4, y4, &q4, &r4);
    CheckPost_div_rem(x4, y4, &q4, &r4);

    // Test case 5: x=7, y=2 -> q=3, r=1
    let x5 = 7; let y5 = 2;
    let (q5, r5) = (3, 1);
    CheckPre_div_rem(x5, y5, &q5, &r5);
    CheckPost_div_rem(x5, y5, &q5, &r5);

    // Test case 8: x=0, y=1 -> q=0, r=0
    let x8 = 0; let y8 = 1;
    let (q8, r8) = (0, 0);
    CheckPre_div_rem(x8, y8, &q8, &r8);
    CheckPost_div_rem(x8, y8, &q8, &r8);

    // Test case 9: x=3, y=4 -> q=0, r=3
    let x9 = 3; let y9 = 4;
    let (q9, r9) = (0, 3);
    CheckPre_div_rem(x9, y9, &q9, &r9);
    CheckPost_div_rem(x9, y9, &q9, &r9);
}

fn invalid_test_harness_div_rem() {
    // Test case 6: Invalid
    let q6 = 0; let r6 = 0;
    CheckPre_div_rem(5, 0, &q6, &r6);

    // Test case 7: Invalid
    let q7 = u32::MAX; let r7 = 0;
    CheckPre_div_rem(7, 0, &q7, &r7);
}

} // verus!