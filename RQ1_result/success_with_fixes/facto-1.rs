#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn factorial(n: int) -> int 
    decreases n,//2E
{
    if (n <= 0) {
        1
    } else {
        n * (factorial(n - 1 as int))
    }
}

#[verifier::external_body]//2a
pub proof fn factorial_monotonic(n1: int, n2: int)//2a
    requires 1 <= n1 <= n2,//2a
    ensures factorial(n1) <= factorial(n2),//2a
{}//2a

pub proof fn factorial_equality(n: int, i: int)//2a
    requires i>=2 && n==factorial(i-1 as int),//2a
    ensures factorial(i) == i*n,//2a
{}//2a

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn facto(n: i32) -> (result: i32)
    requires
        n <= 12,
    ensures
        result == (factorial(n as int)),
{
    if n < 2 {
        proof!{reveal_with_fuel(factorial, 2);} //2A
        return 1;
    }
    let mut res: i32 = 1;
    let mut i: i32 = 2;
    proof!{reveal_with_fuel(factorial, 12);} //2a
    assert(res==factorial(i-1 as int));//2a
    assert(factorial(13)==6227020800);//2a
    assert(factorial(n as int) <= 6227020800) by{//2a
        factorial_monotonic(n as int, 12 as int);//2a
    }//2a
    while i <= n
        invariant
            2 <= i <= n + 1,
            res == (factorial(i - 1 as int)),
        decreases n - i + u128::MAX,//2d
    {
        assert(res * i == factorial(i as int)) by{//2a
            factorial_equality(res as int, i as int);//2a
        }//2a
        assert(res * i <= factorial(n+1 as int)) by{//2a
            factorial_monotonic(i as int, n+1 as int);//2a
        }//2a
        res = res * i;
        i += 1;
    }
    res
}

fn main() {
}

} // verus!
