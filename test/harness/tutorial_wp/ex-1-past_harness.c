// ========== Original Code (with ACSL) ==========
#include <limits.h>

/*@\n  requires a < b  ==> b - a <= INT_MAX ;\n  requires b <= a ==> a - b <= INT_MAX ;\n\n  ensures a < b  ==> a + \\result == b ;\n  ensures b <= a ==> a - \\result == b ;\n*/
int distance(int a, int b){\n  if(a < b) return b - a ;\n  else return a - b ;\n}\n
// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - a < b
void test_case_1() {
    int result = distance(3, 5);
    printf("test_case_1: %d\\n", result);  // Expected: 2
}

// Test case 2: Valid - a > b
void test_case_2() {
    int result = distance(5, 3);
    printf("test_case_2: %d\\n", result);  // Expected: 2
}

// Test case 3: Valid - a is INT_MAX, b is 0
void test_case_3() {
    int result = distance(INT_MAX, 0);
    printf("test_case_3: %d\\n", result);  // Expected: INT_MAX
}

// Test case 4: Valid - a 0, b INT_MAX
void test_case_4() {
    int result = distance(0, INT_MAX);
    printf("test_case_4: %d\\n", result);  // Expected: INT_MAX
}

// Test case 5: Valid - negative numbers
void test_case_5() {
    int result = distance(-5, -3);
    printf("test_case_5: %d\\n", result);  // Expected: 2
}

// Test case 7: Boundary - a INT_MIN+1, b 0
void test_case_7() {
    int result = distance(INT_MIN + 1, 0);
    printf("test_case_7: %d\\n", result);  // Expected: INT_MAX
}

// Test case 8: Invalid - a INT_MIN, b 0
void test_case_8() {
    int result = distance(INT_MIN, 0);
}

// Test case 9: Invalid - a 0, b INT_MIN
void test_case_9() {
    int result = distance(0, INT_MIN);
}

// Harness entry point
void test_harness_distance() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_7();
    test_case_8();
    test_case_9();
}