// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@ requires INT_MIN <= x-y <= INT_MAX;
    ensures y == x-\result;
*/
int diff (int x, int y) {
    return x-y;
}

int main() {
    int t = diff(10, 5);
    //@ assert t == 5;
    return 0;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal subtraction
void test_case_1() {
    int result = diff(10, 5);
    printf("test_case_1: %d\n", result);  // Expected: 5
}

// Test case 2: Valid - negative result
void test_case_2() {
    int result = diff(5, 10);
    printf("test_case_2: %d\n", result);  // Expected: -5
}

// Test case 3: Valid - zero minus negative
void test_case_3() {
    int result = diff(0, -5);
    printf("test_case_3: %d\n", result);  // Expected: 5
}

// Test case 4: Valid - x near max
void test_case_4() {
    int result = diff(INT_MAX - 1, 0);
    printf("test_case_4: %d\n", result);  // Expected: INT_MAX - 1
}

// Test case 5: Valid - x near min
void test_case_5() {
    int result = diff(INT_MIN + 1, 0);
    printf("test_case_5: %d\n", result);  // Expected: INT_MIN + 1
}

// Test case 6: Boundary - x at max
void test_case_6() {
    int result = diff(INT_MAX, 0);
    printf("test_case_6: %d\n", result);  // Expected: INT_MAX
}

// Test case 7: Boundary - x at min
void test_case_7() {
    int result = diff(INT_MIN, 0);
    printf("test_case_7: %d\n", result);  // Expected: INT_MIN
}

// Test case 8: Invalid - underflow
void test_case_8() {
    int result = diff(INT_MIN, 1);  // Frama-C should flag this
}

// Test case 9: Invalid - overflow
void test_case_9() {
    int result = diff(INT_MAX, -1);  // Frama-C should flag this
}

// Harness entry point
void test_harness_diff() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // Invalid test cases are not called for output verification
}