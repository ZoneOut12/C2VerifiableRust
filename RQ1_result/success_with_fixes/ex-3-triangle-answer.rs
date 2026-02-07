#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[derive(PartialEq)]
enum Sides {
    SCALENE,
    ISOSCELE,
    EQUILATERAL,
}

#[derive(PartialEq)]
enum Angles {
    RIGHT,
    ACUTE,
    OBTUSE,
}

use Sides::*;
use Angles::*;

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn sides_kind(a: i32, b: i32, c: i32) -> (result: Sides)
    requires
        0 <= a && 0 <= b && 0 <= c,
        a <= b + c,
        a >= b && a >= c,
    ensures
        (a == b == c) ==> (result == EQUILATERAL),
        (a == b || a == c || b == c) && (a != b || a != c || b != c) ==> (result == ISOSCELE),
        (a != b && a != c && b != c) ==> (result == SCALENE),
{
    if a == b && b == c {
        return EQUILATERAL;
    } else if a == b || b == c || a == c {
        return ISOSCELE;
    } else {
        return SCALENE;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn angles_kind(a: i32, b: i32, c: i32) -> (result: Angles)
    requires
        a <= b + c && a >= b && a >= c,
        0 <= a && a * a <= i32::MAX,
        0 <= b && b * b <= i32::MAX,
        0 <= c && c * c <= i32::MAX,
    ensures
        (a * a > b * b + c * c) ==> (result == OBTUSE),
        (a * a < b * b + c * c) ==> (result == ACUTE),
        (a * a == b * b + c * c) ==> (result == RIGHT),
{
    if a * a - b * b > c * c {
        return OBTUSE;
    } else if a * a - b * b < c * c {
        return ACUTE;
    } else {
        return RIGHT;
    }
}

fn main() {
}

} // verus!
