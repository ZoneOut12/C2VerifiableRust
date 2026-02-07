// ========== Original Code (with ACSL) ==========
/*@ assigns \nothing;
    ensures (((\result>=x0) &&
    (\result>=x1)) &&
    ((\result==x0) || (\result==x1)));
*/
int max(int  x0, int  x1) {
  int x3 = x0 > x1;
  int x4;
  if (x3) {
    x4 = x0;
  } else {
    x4 = x1;
  }
  return x4;
}

// ========== Test Cases ==========
#include <stdio.h>
#include <limits.h>

// Test case 1: Valid - x0 greater than x1
void test_case_1() {
    int result = max(5, 3);
    printf("test_case_1: %d\n", result);  // Expected: 5
}

// Test case 2: Valid - x1 positive and larger
void test_case_2() {
    int result = max(-5, 10);
    printf("test_case_2: %d\n", result);  // Expected: 10
}

// Test case 3: Valid - x0 and x1 equal
void test_case_3() {
    int result = max(0, 0);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - extreme values
void test_case_4() {
    int result = max(INT_MIN, INT_MAX);
    printf("test_case_4: %d\n", result);  // Expected: INT_MAX
}

// Test case 5: Valid - positive and negative
void test_case_5() {
    int result = max(42, -42);
    printf("test_case_5: %d\n", result);  // Expected: 42
}

// Test case 6: Boundary - both INT_MAX
void test_case_6() {
    int result = max(INT_MAX, INT_MAX);
    printf("test_case_8: %d\n", result);  // Expected: INT_MAX
}

// Test case 7: Boundary - both INT_MIN
void test_case_7() {
    int result = max(INT_MIN, INT_MIN);
    printf("test_case_9: %d\n", result);  // Expected: INT_MIN
}

// Harness entry point
void test_harness_max() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
}