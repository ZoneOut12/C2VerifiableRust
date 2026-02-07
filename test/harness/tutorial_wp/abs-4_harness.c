// ========== Original Code (with ACSL) ==========
#include <limits.h>
#include <stdlib.h>

/*@ requires x > INT_MIN;
    assigns \nothing;
    ensures \result >= 0;
*/
int my_abs(int x) {
    return abs(x);
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - Positive integer input
void test_case_1() {
    int result = my_abs(5);
    printf("test_case_1: %d\n", result);  // Expected: 5
}

// Test case 2: Valid - Negative integer input
void test_case_2() {
    int result = my_abs(-10);
    printf("test_case_2: %d\n", result);  // Expected: 10
}

// Test case 3: Valid - Zero input
void test_case_3() {
    int result = my_abs(0);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - Large positive integer
void test_case_4() {
    int result = my_abs(123);
    printf("test_case_4: %d\n", result);  // Expected: 123
}

// Test case 5: Valid - Large negative integer
void test_case_5() {
    int result = my_abs(-456);
    printf("test_case_5: %d\n", result);  // Expected: 456
}

// Test case 6: Boundary - Minimum valid input
void test_case_6() {
    int result = my_abs(-2147483647);
    printf("test_case_6: %d\n", result);  // Expected: 2147483647
}

// Test case 7: Boundary - Maximum valid input
void test_case_7() {
    int result = my_abs(2147483647);
    printf("test_case_7: %d\n", result);  // Expected: 2147483647
}

// Test case 8: Invalid - Input equals INT_MIN
void test_case_8() {
    int result = my_abs(-2147483648);
}

// Test case 9: Invalid - Another violation of precondition
void test_case_9() {
    int result = my_abs(-2147483648);
}

// Harness entry point (not main!)
void test_harness_my_abs() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}
void test_case_8() {
    int x = -2147483648;
    int result = my_abs(x);
}

void test_case_9() {
    int x = -2147483648;
    int result = my_abs(x);
}