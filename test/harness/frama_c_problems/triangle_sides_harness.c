// ========== Original Code (with ACSL) ==========
#include <stdio.h>
#include <limits.h>
/*@
    requires a>0 && b>0 && c>0;
    requires a+b+c <= INT_MAX;
    behavior valid:
        assumes (a+b>c) && (a+c>b) && (b+c>a);
        ensures \result == 1;
    behavior invalid:
        assumes !((a+b>c) && (a+c>b) && (b+c>a));
        ensures \result == 0;
    disjoint behaviors;
    complete behaviors;
*/
int validts(int a, int b, int c) {
    int valid = 0;
    if ((a+b>c) && (a+c>b) && (b+c>a)) {
        valid = 1;
    } else {
        valid = 0;
    }
    return valid;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal triangle
void test_case_1() {
    int result = validts(2, 3, 4);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - equilateral triangle
void test_case_2() {
    int result = validts(5, 5, 5);
    printf("test_case_2: %d\n", result);  // Expected: 1
}

// Test case 3: Valid - right-angled triangle (3,4,5)
void test_case_3() {
    int result = validts(3, 4, 5);
    printf("test_case_3: %d\n", result);  // Expected: 1
}

// Test case 4: Valid - isosceles triangle
void test_case_4() {
    int result = validts(10, 10, 5);
    printf("test_case_4: %d\n", result);  // Expected: 1
}

// Test case 5: Valid - scalene triangle
void test_case_5() {
    int result = validts(7, 10, 15);
    printf("test_case_5: %d\n", result);  // Expected: 1
}

// Test case 6: Invalid - a is zero
void test_case_6() {
    int result = validts(0, 3, 4);
    // No output check for invalid case
}

// Test case 7: Invalid - sum exceeds INT_MAX
void test_case_7() {
    int result = validts(INT_MAX - 1, 1, 1);
    // No output check for invalid case
}

// Test case 8: Boundary - minimal valid triangle
void test_case_8() {
    int result = validts(1, 1, 1);
    printf("test_case_8: %d\n", result);  // Expected: 1
}

// Test case 9: Boundary - sum equals INT_MAX
void test_case_9() {
    int result = validts(INT_MAX - 2, 1, 1);
    printf("test_case_9: %d\n", result);  // Expected: 1
}

// Harness entry point
void test_harness_validts() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6() and test_case_7() intentionally not called
}
#include <limits.h>
void test_case_6() {
    assert(validts(0, 5, 5) == 0);
}
void test_case_7() {
    assert(validts(INT_MAX, 1, 1) == 0);
}