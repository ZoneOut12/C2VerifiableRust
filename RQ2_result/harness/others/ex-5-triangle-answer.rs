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

fn CheckPre_sides_kind(a: i32, b: i32, c: i32)
    requires
        0 <= a && 0 <= b && 0 <= c,
        a <= b + c,
{}

fn CheckPost_sides_kind(a: i32, b: i32, c: i32, result: Sides)
    requires
        (a == b == c) ==> (result == EQUILATERAL),
        (a == b || a == c || b == c) && (a != b || a != c || b != c) ==> (result == ISOSCELE),
        (a != b && a != c && b != c) ==> (result == SCALENE),
{}

fn CheckPre_angles_kind(a: i32, b: i32, c: i32)
    requires
        a <= b + c && a >= b && a >= c,
        0 <= a && a * a <= i32::MAX,
        0 <= b && b * b <= i32::MAX,
        0 <= c && c * c <= i32::MAX,
{}

fn CheckPost_angles_kind(a: i32, b: i32, c: i32, result: Angles)
    requires
        (a * a > b * b + c * c) ==> (result == OBTUSE),
        (a * a < b * b + c * c) ==> (result == ACUTE),
        (a * a == b * b + c * c) ==> (result == RIGHT),
{}


fn CheckPre_classify(a: i32, b: i32, c: i32, old_info: &TriangleInfo)
    requires
        a <= b + c && a >= b && a >= c,
        0 <= a && a * a <= i32::MAX,
        0 <= b && b * b <= i32::MAX,
        0 <= c && c * c <= i32::MAX,
{}

fn CheckPost_classify(a: i32, b: i32, c: i32, info: &TriangleInfo, result: i32)
    requires
        (a > b + c) ==> (result == -1),
        (a <= b + c) ==> (result == 0),
        (a <= b + c && a == b == c) ==> (((*(info))).sides == EQUILATERAL),
        (a <= b + c) && (a == b || a == c || b == c) && (a != b || a != c || b != c) ==> (((*(
        info))).sides == ISOSCELE),
        (a <= b + c && a != b && a != c && b != c) ==> (((*(info))).sides == SCALENE),
        (a <= b + c && a * a > b * b + c * c) ==> (((*(info))).angles == OBTUSE),
        (a <= b + c && a * a < b * b + c * c) ==> (((*(info))).angles == ACUTE),
        (a <= b + c && a * a == b * b + c * c) ==> (((*(info))).angles == RIGHT),
{}

fn main() {
}

fn valid_test_harness_sides_kind() {
    // --- Test Case 1: Equilateral (All sides equal) ---
    // Matches behavior 'equilateral'
    let (a1, b1, c1) = (10, 10, 10);
    CheckPre_sides_kind(a1, b1, c1);
    let result1 = Sides::EQUILATERAL;
    CheckPost_sides_kind(a1, b1, c1, result1);

    // --- Test Case 2: Isosceles (a == b) ---
    // Matches behavior 'isocele'
    let (a2, b2, c2) = (10, 10, 15);
    CheckPre_sides_kind(a2, b2, c2);
    let result2 = Sides::ISOSCELE;
    CheckPost_sides_kind(a2, b2, c2, result2);

    // --- Test Case 3: Isosceles (b == c) ---
    let (a3, b3, c3) = (15, 10, 10);
    CheckPre_sides_kind(a3, b3, c3);
    let result3 = Sides::ISOSCELE;
    CheckPost_sides_kind(a3, b3, c3, result3);

    // --- Test Case 4: Scalene (All sides different) ---
    // Matches behavior 'scalene'
    let (a4, b4, c4) = (3, 4, 5);
    CheckPre_sides_kind(a4, b4, c4);
    let result4 = Sides::SCALENE;
    CheckPost_sides_kind(a4, b4, c4, result4);

    // --- Test Case 5: Boundary - Degenerate triangle (a == b + c) ---
    // Valid per 'requires a <= b + c'
    let (a5, b5, c5) = (20, 10, 10); 
    CheckPre_sides_kind(a5, b5, c5);
    let result5 = Sides::ISOSCELE;
    CheckPost_sides_kind(a5, b5, c5, result5);

    // --- Test Case 6: Boundary - Zero sides ---
    // Valid per 'requires 0 <= a && 0 <= b && 0 <= c'
    let (a6, b6, c6) = (0, 0, 0);
    CheckPre_sides_kind(a6, b6, c6);
    let result6 = Sides::EQUILATERAL;
    CheckPost_sides_kind(a6, b6, c6, result6);

    // --- Test Case 7: Large values ---
    let (a7, b7, c7) = (i32::MAX, i32::MAX, i32::MAX);
    CheckPre_sides_kind(a7, b7, c7);
    let result7 = Sides::EQUILATERAL;
    CheckPost_sides_kind(a7, b7, c7, result7);
}

fn invalid_test_harness_sides_kind() {
    // --- Test Case 8: Negative side length ---
    // Violates: requires 0 <= a
    let (a8, b8, c8) = (-5, 10, 10);
    CheckPre_sides_kind(a8, b8, c8);

    // --- Test Case 9: Violation of Triangle Inequality ---
    // Side 'a' is much larger than the sum of b and c
    // Violates: requires a <= b + c
    let (a9, b9, c9) = (100, 10, 10);
    CheckPre_sides_kind(a9, b9, c9);
}

fn valid_test_harness_angles_kind() {
    // --- Test Case 1: Right Triangle (3, 4, 5) ---
    // 5^2 == 3^2 + 4^2 (25 == 9 + 16)
    let (a1, b1, c1) = (5, 4, 3);
    CheckPre_angles_kind(a1, b1, c1);
    let result1 = Angles::RIGHT;
    CheckPost_angles_kind(a1, b1, c1, result1);

    // --- Test Case 2: Obtuse Triangle ---
    // 6^2 > 4^2 + 4^2 (36 > 16 + 16)
    let (a2, b2, c2) = (6, 4, 4);
    CheckPre_angles_kind(a2, b2, c2);
    let result2 = Angles::OBTUSE;
    CheckPost_angles_kind(a2, b2, c2, result2);

    // --- Test Case 3: Acute Triangle ---
    // 5^2 < 4^2 + 4^2 (25 < 16 + 16)
    let (a3, b3, c3) = (5, 4, 4);
    CheckPre_angles_kind(a3, b3, c3);
    let result3 = Angles::ACUTE;
    CheckPost_angles_kind(a3, b3, c3, result3);

    // --- Test Case 4: Degenerate Triangle (Flat) ---
    // a = b + c (10 = 5 + 5). 100 > 25 + 25
    let (a4, b4, c4) = (10, 5, 5);
    CheckPre_angles_kind(a4, b4, c4);
    let result4 = Angles::OBTUSE;
    CheckPost_angles_kind(a4, b4, c4, result4);

    // --- Test Case 5: Equilateral Triangle (Always Acute) ---
    // 2^2 < 2^2 + 2^2 (4 < 4 + 4)
    let (a5, b5, c5) = (2, 2, 2);
    CheckPre_angles_kind(a5, b5, c5);
    let result5 = Angles::ACUTE;
    CheckPost_angles_kind(a5, b5, c5, result5);

    // --- Test Case 6: Minimum Non-Zero Values ---
    let (a6, b6, c6) = (1, 1, 1);
    CheckPre_angles_kind(a6, b6, c6);
    let result6 = Angles::ACUTE;
    CheckPost_angles_kind(a6, b6, c6, result6);

    // --- Test Case 7: Boundary - Squares near INT_MAX ---
    // 46340^2 = 2147395600 (less than 2147483647)
    let (a7, b7, c7) = (46340, 40000, 20000);
    CheckPre_angles_kind(a7, b7, c7);
    let result7 = Angles::OBTUSE;
    CheckPost_angles_kind(a7, b7, c7, result7);
}

fn invalid_test_harness_angles_kind() {
    // --- Test Case 8: Invalid - Side 'a' is not the longest ---
    // Violates: requires a >= b
    let (a8, b8, c8) = (3, 5, 4);
    CheckPre_angles_kind(a8, b8, c8);

    // --- Test Case 9: Invalid - Potential Overflow ---
    // 50000^2 = 2,500,000,000 (Greater than i32::MAX)
    // Violates: requires a*a <= INT_MAX
    let (a9, b9, c9) = (50000, 10, 10);
    CheckPre_angles_kind(a9, b9, c9);
}

fn valid_test_harness_classify() {
    // A default info object to be mutated
    let mut info = TriangleInfo { sides: Sides::SCALENE, angles: Angles::ACUTE };

    // --- Test Case 1: Equilateral triangle ---
    let (a1, b1, c1) = (3, 3, 3);
    CheckPre_classify(a1, b1, c1, &info);
    // Logic: result = 0, sides = EQUILATERAL, angles = ACUTE
    info.sides = Sides::EQUILATERAL; info.angles = Angles::ACUTE;
    CheckPost_classify(a1, b1, c1, &info, 0);

    // --- Test Case 2: Isosceles triangle ---
    let (a2, b2, c2) = (5, 5, 3);
    CheckPre_classify(a2, b2, c2, &info);
    info.sides = Sides::ISOSCELE; info.angles = Angles::ACUTE;
    CheckPost_classify(a2, b2, c2, &info, 0);

    // --- Test Case 3: Scalene triangle ---
    let (a3, b3, c3) = (7, 6, 5);
    CheckPre_classify(a3, b3, c3, &info);
    info.sides = Sides::SCALENE; info.angles = Angles::ACUTE;
    CheckPost_classify(a3, b3, c3, &info, 0);

    // --- Test Case 4: Right-angled triangle ---
    let (a4, b4, c4) = (5, 4, 3);
    CheckPre_classify(a4, b4, c4, &info);
    info.sides = Sides::SCALENE; info.angles = Angles::RIGHT;
    CheckPost_classify(a4, b4, c4, &info, 0);

    // --- Test Case 5: Obtuse triangle ---
    let (a5, b5, c5) = (6, 3, 4);
    CheckPre_classify(a5, b5, c5, &info);
    info.sides = Sides::SCALENE; info.angles = Angles::OBTUSE;
    CheckPost_classify(a5, b5, c5, &info, 0);

    // --- Test Case 8: Boundary - a = b + c (Degenerate) ---
    let (a8, b8, c8) = (5, 2, 3);
    CheckPre_classify(a8, b8, c8, &info);
    info.sides = Sides::SCALENE; info.angles = Angles::OBTUSE;
    CheckPost_classify(a8, b8, c8, &info, 0);

    // --- Test Case 9: Boundary - Zero length ---
    let (a9, b9, c9) = (0, 0, 0);
    CheckPre_classify(a9, b9, c9, &info);
    info.sides = Sides::EQUILATERAL; 
    info.angles = Angles::RIGHT;
    CheckPost_classify(a9, b9, c9, &info, 0);
}

fn invalid_test_harness_classify() {
    let mut info = TriangleInfo { sides: Sides::SCALENE, angles: Angles::ACUTE };

    // --- Test Case 6: Invalid - a > b + c ---
    let (a6, b6, c6) = (10, 2, 3);
    CheckPre_classify(a6, b6, c6, &info);

    // --- Test Case 7: Invalid - negative side length ---
    let (a7, b7, c7) = (-1, 2, 3);
    CheckPre_classify(a7, b7, c7, &info);
}

} // verus!
