// ========== Original Code (with ACSL) ==========
/*@\n  ensures \\result >= a && \\result >= b;\n  ensures \\result == a || \\result == b;\n*/\nint max(int a, int b){\n  return (a > b) ? a : b;\n}\n\nvoid foo(){\n  int a = 42;\n  int b = 37;\n  int c = max(a,b);\n\n  //@assert c == 42;\n}\n\n// ========== Test Cases ==========
#include <stdio.h>
#include <limits.h>

// Test case 1: Valid - a > b
void test_case_1() {
    int result = max(5, 3);
    printf("test_case_1: %d\n", result);  // Expected: 5
}

// Test case 2: Valid - b > a with negative a
void test_case_2() {
    int result = max(-2, 10);
    printf("test_case_2: %d\n", result);  // Expected: 10
}

// Test case 3: Valid - a and b equal and negative
void test_case_3() {
    int result = max(-5, -5);
    printf("test_case_3: %d\n", result);  // Expected: -5
}

// Test case 4: Valid - a greater than b with both negative
void test_case_4() {
    int result = max(-1, -10);
    printf("test_case_4: %d\n", result);  // Expected: -1
}

// Test case 5: Valid - a positive and b negative
void test_case_5() {
    int result = max(5, -3);
    printf("test_case_5: %d\n", result);  // Expected: 5
}

// Test case 6: Boundary - a and b at maximum integer value
void test_case_6() {
    int result = max(INT_MAX, INT_MAX);
    printf("test_case_6: %d\n", result);  // Expected: INT_MAX
}

// Test case 7: Boundary - a at minimum integer value and b larger
void test_case_7() {
    int result = max(INT_MIN, -100);
    printf("test_case_7: %d\n", result);  // Expected: -100
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
#include <limits.h>
void test_case_1() { assert(max(5, 3) == 5); }
void test_case_2() { assert(max(-1, -5) == -1); }
void test_case_3() { assert(max(0, 0) == 0); }
void test_case_4() { assert(max(INT_MAX, INT_MIN) == INT_MAX); }
void test_case_5() { assert(max(123456, 654321) == 654321); }
void test_case_6() { assert(max(INT_MAX, INT_MAX) == INT_MAX); }
void test_case_7() { assert(max(INT_MIN, INT_MIN) == INT_MIN); }