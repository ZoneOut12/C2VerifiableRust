// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@
requires (x0<INT_MAX);
assigns \nothing;
ensures (\result>x0);
*/
int inc(int  x0) {
  int x2 = x0 + 1;
  return x2;
}

// ========== Test Cases ==========
#include <stdio.h>
#include <limits.h>

// Test case 1: Valid - zero
void test_case_1() {
    int result = inc(0);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - positive number
void test_case_2() {
    int result = inc(42);
    printf("test_case_2: %d\n", result);  // Expected: 43
}

// Test case 3: Valid - negative number
void test_case_3() {
    int result = inc(-10);
    printf("test_case_3: %d\n", result);  // Expected: -9
}

// Test case 4: Valid - mid-range positive
void test_case_4() {
    int result = inc(1000);
    printf("test_case_4: %d\n", result);  // Expected: 1001
}

// Test case 5: Valid - near INT_MAX (INT_MAX=2147483647)
void test_case_5() {
    int result = inc(INT_MAX - 100);
    printf("test_case_5: %d\n", result);  // Expected: INT_MAX -99
}

// Test case 6: Boundary - INT_MAX-1
void test_case_6() {
    int result = inc(INT_MAX - 1);
    printf("test_case_6: %d\n", result);  // Expected: INT_MAX
}

// Test case 7: Boundary - INT_MIN
void test_case_7() {
    int result = inc(INT_MIN);
    printf("test_case_7: %d\n", result);  // Expected: INT_MIN +1
}

// Test case 8: Invalid - x0 == INT_MAX
void test_case_8() {
    int result = inc(INT_MAX);  // Frama-C should flag this
}

// Test case 9: Invalid - x0 == INT_MAX (duplicate)
void test_case_9() {
    int result = inc(INT_MAX);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_inc() {
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
    ASSERT_EQUAL(inc(2147483647), -2147483648);
}

void test_case_9() {
    ASSERT_EQUAL(inc(2147483647), -2147483648);
}