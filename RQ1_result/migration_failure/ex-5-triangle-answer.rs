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

struct TriangleInfo {
    sides: Sides,
    angles: Angles,
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn sides_kind(a: i32, b: i32, c: i32) -> (result: Sides)
    requires
        0 <= a && 0 <= b && 0 <= c,
        a <= b + c,
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

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn classify(a: i32, b: i32, c: i32, info: &mut TriangleInfo) -> (result: i32)
    requires
        true,
        a <= b + c && a >= b && a >= c,
        0 <= a && a * a <= i32::MAX,
        0 <= b && b * b <= i32::MAX,
        0 <= c && c * c <= i32::MAX,
    ensures
        (a > b + c) ==> (result == -1),
        (a <= b + c) ==> (result == 0),
        (a <= b + c && a == b == c) ==> ((((info)@)).sides == EQUILATERAL),
        (a <= b + c) && (a == b || a == c || b == c) && (a != b || a != c || b != c) ==> ((((
        info)@)).sides == ISOSCELE),
        (a <= b + c && a != b && a != c && b != c) ==> ((((info)@)).sides == SCALENE),
        (a <= b + c && a * a > b * b + c * c) ==> ((((info)@)).angles == OBTUSE),
        (a <= b + c && a * a < b * b + c * c) ==> ((((info)@)).angles == ACUTE),
        (a <= b + c && a * a == b * b + c * c) ==> ((((info)@)).angles == RIGHT),
{
    if a > b + c {
        return -1;
    }
    info.sides = sides_kind(a, b, c);
    info.angles = angles_kind(a, b, c);
    return 0;
}

fn main() {
}

} // verus!
