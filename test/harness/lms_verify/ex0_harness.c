// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@ requires x < INT_MAX;
    ensures \result > x;
*/
int inc (int x) { return x+1; }

// ========== Test Cases ==========
#include <stdio.h>

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

// Test case 5: Valid - near upper bound (INT_MAX-2)
void test_case_5() {
    int result = inc(2147483645);
    printf("test_case_5: %d\n", result);  // Expected: 2147483646
}

// Test case 6: Boundary - maximum allowed value (INT_MAX-1)
void test_case_6() {
    int result = inc(2147483646);
    printf("test_case_6: %d\n", result);  // Expected: 2147483647
}

// Test case 7: Boundary - minimum integer value (INT_MIN)
void test_case_7() {
    int result = inc(-2147483648);
    printf("test_case_7: %d\n", result);  // Expected: -2147483647
}

// Test case 8: Invalid - x equals INT_MAX
void test_case_8() {
    int result = inc(2147483647);  // Frama-C should flag this
}

// Test case 9: Invalid - x exceeds INT_MAX (overflow value)
void test_case_9() {
    int result = inc(2147483648);  // Frama-C should flag this
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
    ASSERT_EQ(2147483648, inc(INT_MAX));
}

void test_case_9() {
    ASSERT_EQ(2147483648, inc(INT_MAX));
}