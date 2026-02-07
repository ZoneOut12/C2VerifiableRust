// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@
    requires INT_MIN <= *a + *b <= INT_MAX;
    requires \valid(a) && \valid_read(b);
    requires \separated(a, b);
    assigns *a;
    ensures *a == \old(*a) + *b;
    ensures *b == \old(*b);
*/
int incr_a_by_b(int* a, int const* b){
    *a += *b;
    return *a;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - positive integers
void test_case_1() {
    int a = 5;
    int b = 3;
    int result = incr_a_by_b(&a, &b);
    printf("test_case_1: a=%d, result=%d\n", a, result);  // Expected: a=8, result=8
}

// Test case 2: Valid - negative integers
void test_case_2() {
    int a = -2;
    int b = -3;
    int result = incr_a_by_b(&a, &b);
    printf("test_case_2: a=%d, result=%d\n", a, result);  // Expected: a=-5, result=-5
}

// Test case 3: Valid - mixed sign integers
void test_case_3() {
    int a = 10;
    int b = -5;
    int result = incr_a_by_b(&a, &b);
    printf("test_case_3: a=%d, result=%d\n", a, result);  // Expected: a=5, result=5
}

// Test case 4: Valid - zero and positive integer
void test_case_4() {
    int a = 0;
    int b = 42;
    int result = incr_a_by_b(&a, &b);
    printf("test_case_4: a=%d, result=%d\n", a, result);  // Expected: a=42, result=42
}

// Test case 5: Valid - zero sum
void test_case_5() {
    int a = -100;
    int b = 100;
    int result = incr_a_by_b(&a, &b);
    printf("test_case_5: a=%d, result=%d\n", a, result);  // Expected: a=0, result=0
}

// Test case 6: Boundary - sum equals INT_MAX
void test_case_6() {
    int a = INT_MAX;
    int b = 0;
    int result = incr_a_by_b(&a, &b);
    printf("test_case_6: a=%d, result=%d\n", a, result);  // Expected: a=INT_MAX, result=INT_MAX
}

// Test case 7: Boundary - sum equals INT_MIN
void test_case_7() {
    int a = INT_MIN;
    int b = 0;
    int result = incr_a_by_b(&a, &b);
    printf("test_case_7: a=%d, result=%d\n", a, result);  // Expected: a=INT_MIN, result=INT_MIN
}

// Test case 8: Invalid - NULL pointer for a
void test_case_8() {
    int b = 5;
    int result = incr_a_by_b(NULL, &b);  // Frama-C should flag this
}

// Test case 9: Invalid - overlapping pointers
void test_case_9() {
    int a = 5;
    int const *b = &a;
    int result = incr_a_by_b((int *)b, b);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_incr_a_by_b() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called - for precondition testing
}