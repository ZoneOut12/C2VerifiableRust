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

fn sides_kind(a: i32, b: i32, c: i32) -> Sides {
    if a == b && b == c {
        return EQUILATERAL;
    } else if a == b || b == c || a == c {
        return ISOSCELE;
    } else {
        return SCALENE;
    }
}

fn angles_kind(a: i32, b: i32, c: i32) -> Angles {
    if a * a - b * b > c * c {
        return OBTUSE;
    } else if a * a - b * b < c * c {
        return ACUTE;
    } else {
        return RIGHT;
    }
}