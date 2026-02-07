// ========== Original Code (with ACSL) ==========
#include <limits.h>

enum Sides { SCALENE, ISOSCELE, EQUILATERAL };
enum Angles { RIGHT, ACUTE, OBTUSE };

/*@
  requires 0 <= a && 0 <= b && 0 <= c;
  requires a <= b+c;
  requires a >= b && a >= c;

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
enum Sides sides_kind(int a, int b, int c) {
  if (a == b && b == c) {
    return EQUILATERAL ;
  } else if (a == b || b == c || a == c) {
    return ISOSCELE ;
  } else {
    return SCALENE ;
  }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - equilateral
void test_case_1() {
    enum Sides result = sides_kind(3, 3, 3);
    printf("test_case_1: %d\n", result);  // Expected: 0 (EQUILATERAL)
}

// Test case 2: Valid - isosceles
void test_case_2() {
    enum Sides result = sides_kind(5, 5, 3);
    printf("test_case_2: %d\n", result);  // Expected: 1 (ISOSCELE)
}

// Test case 3: Valid - scalene
void test_case_3() {
    enum Sides result = sides_kind(5, 4, 3);
    printf("test_case_3: %d\n", result);  // Expected: 2 (SCALENE)
}

// Test case 4: Valid - edge case (a = b + c)
void test_case_4() {
    enum Sides result = sides_kind(5, 3, 2);
    printf("test_case_4: %d\n", result);  // Expected: 1 (ISOSCELE)
}

// Test case 5: Valid - zero-length sides
void test_case_5() {
    enum Sides result = sides_kind(0, 0, 0);
    printf("test_case_5: %d\n", result);  // Expected: 0 (EQUILATERAL)
}

// Test case 6: Invalid - negative side length
void test_case_6() {
    enum Sides result = sides_kind(-1, 2, 2);  // Frama-C should flag this
}

// Test case 7: Invalid - a not largest side
void test_case_7() {
    enum Sides result = sides_kind(3, 4, 5);  // Frama-C should flag this
}

// Test case 8: Boundary - minimum difference
void test_case_8() {
    enum Sides result = sides_kind(5, 3, 3);
    printf("test_case_8: %d\n", result);  // Expected: 1 (ISOSCELE)
}

// Test case 9: Boundary - smallest positive values
void test_case_9() {
    enum Sides result = sides_kind(1, 1, 1);
    printf("test_case_9: %d\n", result);  // Expected: 0 (EQUILATERAL)
}

// Harness entry point
void test_harness_sides_kind() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // test_case_6 and test_case_7 intentionally not called
    test_case_8();
    test_case_9();
}
void test_case_6() {
    assert(sides_kind(5, 2, 2) == SIDES_INVALID);
}

void test_case_7() {
    assert(sides_kind(3, 4, 5) == SIDES_INVALID);
}