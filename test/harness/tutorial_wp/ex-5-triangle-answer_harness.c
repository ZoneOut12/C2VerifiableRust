// ========== Original Code (with ACSL) ==========
#include <limits.h>

enum Sides { SCALENE, ISOSCELE, EQUILATERAL };
enum Angles { RIGHT, ACUTE, OBTUSE };

struct TriangleInfo {
  enum Sides sides;
  enum Angles angles;
};

/*@
  requires 0 <= a && 0 <= b && 0 <= c;
  requires a <= b+c;

  assigns \nothing;

  behavior equilateral:
    assumes a == b == c ;
    ensures \result == EQUILATERAL;

  behavior isocele:
    assumes a == b || a == c || b == c ;
    assumes a != b || a != c || b != c ;
    ensures \result == ISOSCELE;

  behavior scalene:
    assumes a != b && a != c && b != c ;
    ensures \result == SCALENE;
  
  disjoint behaviors;
  complete behaviors;
*/
enum Sides sides_kind(int a, int b, int c){
  if(a == b && b == c){
    return EQUILATERAL ;
  } else if(a == b || b == c || a == c){
    return ISOSCELE ;
  } else {
    return SCALENE ;
  }
}

/*@
  requires a <= b+c && a >= b && a >= c ;
  requires 0 <= a && a*a <= INT_MAX;
  requires 0 <= b && b*b <= INT_MAX;
  requires 0 <= c && c*c <= INT_MAX;
  
  assigns \nothing;

  behavior obtuse:
    assumes a*a > b*b + c*c;
    ensures \result == OBTUSE;

  behavior acute:
    assumes a*a < b*b + c*c;
    ensures \result == ACUTE;

  behavior right:
    assumes a*a == b*b + c*c;
    ensures \result == RIGHT;

  disjoint behaviors;
  complete behaviors;
*/
enum Angles angles_kind(int a, int b, int c){
  if(a*a - b*b > c*c){
    return OBTUSE;
  } else if(a*a - b*b < c*c){
    return ACUTE;
  } else {
    return RIGHT;
  }
}

/*@
  requires \valid(info);
  requires a <= b+c && a >= b && a >= c ;
  requires 0 <= a && a*a <= INT_MAX;
  requires 0 <= b && b*b <= INT_MAX;
  requires 0 <= c && c*c <= INT_MAX;

  assigns *info;
  
  behavior not_a_triangle:
    assumes a > b+c ;
    ensures \result == -1;

  behavior triangle:
    assumes a <= b+c ;
    ensures \result == 0;

  behavior equilateral:
    assumes a <= b+c && a == b == c ;
    ensures (*info).sides == EQUILATERAL;

  behavior isocele:
    assumes a <= b+c ;
    assumes a == b || a == c || b == c ;
    assumes a != b || a != c || b != c ;
    ensures (*info).sides == ISOSCELE;

  behavior scalene:
    assumes a <= b+c && a != b && a != c && b != c ;
    ensures (*info).sides == SCALENE;

  behavior obtuse:
    assumes a <= b+c && a*a > b*b + c*c ;
    ensures (*info).angles == OBTUSE;

  behavior acute:
    assumes a <= b+c && a*a < b*b + c*c ;
    ensures (*info).angles == ACUTE;

  behavior right:
    assumes a <= b+c && a*a == b*b + c*c ;
    ensures (*info).angles == RIGHT;

  disjoint behaviors triangle, not_a_triangle;
  complete behaviors triangle, not_a_triangle;

  disjoint behaviors equilateral, isocele, scalene;
  complete behaviors equilateral, isocele, scalene, not_a_triangle;

  disjoint behaviors obtuse, acute, right;
  complete behaviors obtuse, acute, right, not_a_triangle;
*/
int classify(int a, int b, int c, struct TriangleInfo* info){
  if(a > b+c) return -1;

  info->sides  = sides_kind(a, b, c);
  info->angles = angles_kind(a, b, c);

  return 0;
}

// ========== Test Cases ==========
#include <stdio.h>
#include <assert.h>

// Test case 1: Valid - equilateral triangle
void test_case_1() {
    struct TriangleInfo info;
    int result = classify(3, 3, 3, &info);
    printf("test_case_1: %d (sides: %d, angles: %d)\n", result, info.sides, info.angles);
}

// Test case 2: Valid - isosceles triangle
void test_case_2() {
    struct TriangleInfo info;
    int result = classify(5, 5, 3, &info);
    printf("test_case_2: %d (sides: %d, angles: %d)\n", result, info.sides, info.angles);
}

// Test case 3: Valid - scalene triangle
void test_case_3() {
    struct TriangleInfo info;
    int result = classify(7, 6, 5, &info);
    printf("test_case_3: %d (sides: %d, angles: %d)\n", result, info.sides, info.angles);
}

// Test case 4: Valid - right-angled triangle
void test_case_4() {
    struct TriangleInfo info;
    int result = classify(5, 3, 4, &info);
    printf("test_case_4: %d (sides: %d, angles: %d)\n", result, info.sides, info.angles);
}

// Test case 5: Valid - obtuse triangle
void test_case_5() {
    struct TriangleInfo info;
    int result = classify(6, 3, 4, &info);
    printf("test_case_5: %d (sides: %d, angles: %d)\n", result, info.sides, info.angles);
}

// Test case 6: Invalid - a > b + c
void test_case_6() {
    struct TriangleInfo info;
    int result = classify(10, 2, 3, &info);
    printf("test_case_6: %d\n", result);
}

// Test case 7: Invalid - negative side length
void test_case_7() {
    struct TriangleInfo info;
    int result = classify(-1, 2, 3, &info);
    printf("test_case_7: %d\n", result);
}

// Test case 8: Boundary - a = b + c
void test_case_8() {
    struct TriangleInfo info;
    int result = classify(5, 2, 3, &info);
    printf("test_case_8: %d (sides: %d, angles: %d)\n", result, info.sides, info.angles);
}

// Test case 9: Boundary - zero-length sides
void test_case_9() {
    struct TriangleInfo info;
    int result = classify(0, 0, 0, &info);
    printf("test_case_9: %d (sides: %d, angles: %d)\n", result, info.sides, info.angles);
}

// Harness entry point
void test_harness_classify() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    test_case_8();
    test_case_9();
}

void test_harness_sides_kind() {
    // Valid 1: Equilateral
    assert(sides_kind(5, 5, 5) == EQUILATERAL);

    // Valid 2: Isosceles (first two)
    assert(sides_kind(10, 10, 12) == ISOSCELE);

    // Valid 3: Isosceles (last two)
    assert(sides_kind(12, 10, 10) == ISOSCELE);

    // Valid 4: Scalene
    assert(sides_kind(7, 8, 9) == SCALENE);

    // Valid 5: Degenerate triangle (flat)
    assert(sides_kind(10, 5, 5) == ISOSCELE);

    // Valid 6: All zeros
    assert(sides_kind(0, 0, 0) == EQUILATERAL);

    // Valid 7: Maximum integers
    assert(sides_kind(INT_MAX, INT_MAX, INT_MAX) == EQUILATERAL);

    // Invalid 8: Negative side
    // sides_kind(-1, 5, 5); // Frama-C flags this

    // Invalid 9: Impossible triangle
    // sides_kind(50, 1, 1); // Frama-C flags this
}

void test_harness_angles_kind() {
    // Valid 1: Right
    assert(angles_kind(5, 4, 3) == RIGHT);

    // Valid 2: Obtuse
    assert(angles_kind(6, 4, 4) == OBTUSE);

    // Valid 3: Acute
    assert(angles_kind(5, 4, 4) == ACUTE);

    // Valid 4: Flat Obtuse
    assert(angles_kind(10, 5, 5) == OBTUSE);

    // Valid 5: Equilateral
    assert(angles_kind(2, 2, 2) == ACUTE);

    // Valid 6: Smallest
    assert(angles_kind(1, 1, 1) == ACUTE);

    // Valid 7: Large within INT_MAX
    assert(angles_kind(46340, 46340, 0) == RIGHT);

    // Invalid 8: Incorrect longest side
    // angles_kind(3, 10, 4); 

    // Invalid 9: Square overflow
    // angles_kind(60000, 5, 5); 
}