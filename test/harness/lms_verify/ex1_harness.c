// ========== Original Code (with ACSL) ==========
/*@ ensures \\result >= x && \\result >= y;
    ensures \\result == x || \\result == y;
*/
int max (int x, int y) { return (x > y) ? x : y; }

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - x greater than y
void test_case_1() {
    int result = max(5, 3);
    printf("test_case_1: %d\\n", result);  // Expected: 5
}

// Test case 2: Valid - y greater than x
void test_case_2() {
    int result = max(-2, 3);
    printf("test_case_2: %d\\n", result);  // Expected: 3
}

// Test case 3: Valid - x is zero
void test_case_3() {
    int result = max(0, -5);
    printf("test_case_3: %d\\n", result);  // Expected: 0
}

// Test case 4: Valid - both negative
void test_case_4() {
    int result = max(-5, -3);
    printf("test_case_4: %d\\n", result);  // Expected: -3
}

// Test case 5: Valid - large x
void test_case_5() {
    int result = max(42, 10);
    printf("test_case_5: %d\\n", result);  // Expected: 42
}

// Test case 6: Boundary - equal positive
void test_case_6() {
    int result = max(10, 10);
    printf("test_case_6: %d\\n", result);  // Expected: 10
}

// Test case 7: Boundary - equal negative
void test_case_7() {
    int result = max(-5, -5);
    printf("test_case_7: %d\\n", result);  // Expected: -5
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