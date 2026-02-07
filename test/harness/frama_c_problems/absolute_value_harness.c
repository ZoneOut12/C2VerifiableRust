// ========== Original Code (with ACSL) ==========
#include <limits.h>
#include <stdlib.h>

/*@
    requires val > INT_MIN;
    ensures \result >= 0;
    ensures (val >= 0 ==> \result == val) && 
            (val < 0 ==> \result == -val);
*/
int my_abs(int val) {
    return abs(x);
}

/*@
    requires a > INT_MIN;
*/
void foo(int a) {
    int b = my_abs(-42);
    int c = my_abs(42);
    int d = my_abs(a);
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - zero
void test_case_1() {
    int val = 0;
    int result = my_abs(val);
    printf("test_case_1: %d\n", result);  // Expected: 0
}

// Test case 2: Valid - positive number
void test_case_2() {
    int val = 42;
    int result = my_abs(val);
    printf("test_case_2: %d\n", result);  // Expected: 42
}

// Test case 3: Valid - negative number
void test_case_3() {
    int val = -42;
    int result = my_abs(val);
    printf("test_case_3: %d\n", result);  // Expected: 42
}

// Test case 4: Valid - positive large number
void test_case_4() {
    int val = 1000;
    int result = my_abs(val);
    printf("test_case_4: %d\n", result);  // Expected: 1000
}

// Test case 5: Valid - negative large number
void test_case_5() {
    int val = -1000;
    int result = my_abs(val);
    printf("test_case_5: %d\n", result);  // Expected: 1000
}

// Test case 6: Invalid - INT_MIN
void test_case_6() {
    int val = INT_MIN;
    int result = my_abs(val);  // Frama-C should flag this
}

// Test case 7: Invalid - explicit INT_MIN value
void test_case_7() {
    int val = -2147483648;
    int result = my_abs(val);  // Frama-C should flag this
}

// Test case 8: Boundary - minimal valid negative input
void test_case_8() {
    int val = -2147483647;
    int result = my_abs(val);
    printf("test_case_8: %d\n", result);  // Expected: 2147483647
}

// Test case 9: Boundary - zero
void test_case_9() {
    int val = 0;
    int result = my_abs(val);
    printf("test_case_9: %d\n", result);  // Expected: 0
}

// Harness entry point
void test_harness_abs() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6() and test_case_7() intentionally not called
}