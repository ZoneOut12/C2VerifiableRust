// ========== Original Code (with ACSL) ==========
//@ predicate is_pos(int x) = x > 0;
//@ predicate is_nat(int x) = x >= 0;

/*@ requires is_pos(x);
    ensures is_nat(\\result);
*/
int minus1(int x) {
  return x-1;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid input x=2
void test_case_1() {
    int x = 2;
    int result = minus1(x);
    printf("test_case_1: %d\\n", result); // Expected: 1
}

// Test case 2: Valid input x=5
void test_case_2() {
    int x = 5;
    int result = minus1(x);
    printf("test_case_2: %d\\n", result); // Expected: 4
}

// Test case 3: Valid input x=10
void test_case_3() {
    int x = 10;
    int result = minus1(x);
    printf("test_case_3: %d\\n", result); // Expected: 9
}

// Test case 4: Valid input x=42
void test_case_4() {
    int x = 42;
    int result = minus1(x);
    printf("test_case_4: %d\\n", result); // Expected: 41
}

// Test case 5: Valid input x=100
void test_case_5() {
    int x = 100;
    int result = minus1(x);
    printf("test_case_5: %d\\n", result); // Expected: 99
}

// Test case 6: Invalid input x=0
void test_case_6() {
    int x = 0;
    int result = minus1(x); // Frama-C should flag this
}

// Test case 7: Invalid input x=-5
void test_case_7() {
    int x = -5;
    int result = minus1(x); // Frama-C should flag this
}

// Test case 8: Boundary case x=1
void test_case_8() {
    int x = 1;
    int result = minus1(x);
    printf("test_case_8: %d\\n", result); // Expected: 0
}

// Test case 9: Boundary case x=2
void test_case_9() {
    int x = 2;
    int result = minus1(x);
    printf("test_case_9: %d\\n", result); // Expected: 1
}

// Harness entry point (not main!)
void test_harness_minus1() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // Invalid cases intentionally not called
}