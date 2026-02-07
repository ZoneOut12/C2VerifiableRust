// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@ requires x+y <= INT_MAX;
    requires x+y >= INT_MIN;
    ensures \result == x+y;
*/
int add(int x, int y) {
    return x+y;
}

void foo() {
    int a = add(1, 43);
}

// ========== Test Cases ==========
#include <stdio.h>
#include <limits.h>

// Test case 1: Valid - normal case from foo
void test_case_1() {
    int result = add(1, 43);
    printf("test_case_1: %d\n", result);  // Expected: 44
}

// Test case 2: Valid - small positive numbers
void test_case_2() {
    int result = add(10, 20);
    printf("test_case_2: %d\n", result);  // Expected: 30
}

// Test case 3: Valid - zeros
void test_case_3() {
    int result = add(0, 0);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - negative and positive
void test_case_4() {
    int result = add(-5, 3);
    printf("test_case_4: %d\n", result);  // Expected: -2
}

// Test case 5: Valid - sum at INT_MAX
void test_case_5() {
    int result = add(INT_MAX - 1, 1);
    printf("test_case_5: %d\n", result);  // Expected: INT_MAX
}

// Test case 6: Invalid - sum exceeds INT_MAX
void test_case_6() {
    int result = add(INT_MAX, 1);  // Frama-C should flag this
}

// Test case 7: Invalid - sum below INT_MIN
void test_case_7() {
    int result = add(INT_MIN, -1);  // Frama-C should flag this
}

// Test case 8: Boundary - sum equals INT_MAX
void test_case_8() {
    int result = add(INT_MAX, 0);
    printf("test_case_8: %d\n", result);  // Expected: INT_MAX
}

// Test case 9: Boundary - sum equals INT_MIN
void test_case_9() {
    int result = add(INT_MIN, 0);
    printf("test_case_9: %d\n", result);  // Expected: INT_MIN
}

// Harness entry point (not main!)
void test_harness_add() {
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
    int result = add(2147483647, 1);
}
void test_case_7() {
    int result = add(-2147483648, -1);
}