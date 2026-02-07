// ========== Original Code (with ACSL) ==========
/*@
    ensures \result == x || \result == y;
    ensures \result >= x && \result >= y;
*/
int max(int x, int y) {
    if (x >= y) {
        return x;
    }
    return y;
}

// ========== Test Cases ==========
#include <stdio.h>
#include <limits.h>

// Test case 1: Valid - x greater than y
void test_case_1() {
    int result = max(5, 3);
    printf("test_case_1: %d\n", result);  // Expected: 5
}

// Test case 2: Valid - y greater than x
void test_case_2() {
    int result = max(2, 4);
    printf("test_case_2: %d\n", result);  // Expected: 4
}

// Test case 3: Valid - x equals y
void test_case_3() {
    int result = max(7, 7);
    printf("test_case_3: %d\n", result);  // Expected: 7
}

// Test case 4: Valid - x is zero, y is negative
void test_case_4() {
    int result = max(0, -5);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid - both negative, x greater
void test_case_5() {
    int result = max(-1, -3);
    printf("test_case_5: %d\n", result);  // Expected: -1
}

// Test case 6: Boundary - maximum integer values
void test_case_6() {
    int result = max(INT_MAX, INT_MAX);
    printf("test_case_6: %d\n", result);  // Expected: 2147483647
}

// Test case 7: Boundary - minimum integer values
void test_case_7() {
    int result = max(INT_MIN, INT_MIN);
    printf("test_case_7: %d\n", result);  // Expected: -2147483648
}


// Harness entry point (not main!)
void test_harness_max() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
}