// ========== Original Code (with ACSL) ==========
#include<limits.h>
/*@ requires p>=5000;
    requires r> 0 && r <15;
    requires n > 0 && n < 5;
    requires p*n*r <= INT_MAX;
    ensures \result <= 2*p && \result >0;
    ensures p*n*r <= 200*p*n*r;
@*/
int simple(int p,int n,int r)
{
    int si;
    si = p*n*r/100;
    return si;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - minimum values
void test_case_1() {
    int result = simple(5000, 1, 1);
    printf("test_case_1: %d\n", result);  // Expected: 50
}

// Test case 2: Valid - original example
void test_case_2() {
    int result = simple(10000, 3, 10);
    printf("test_case_2: %d\n", result);  // Expected: 3000
}

// Test case 3: Valid - mid-range values
void test_case_3() {
    int result = simple(7500, 2, 5);
    printf("test_case_3: %d\n", result);  // Expected: 750
}

// Test case 4: Boundary - max n and r
void test_case_4() {
    int result = simple(5000, 4, 14);
    printf("test_case_4: %d\n", result);  // Expected: 2800
}

// Test case 5: Boundary - min n and max r
void test_case_5() {
    int result = simple(5000, 1, 14);
    printf("test_case_5: %d\n", result);  // Expected: 700
}

// Test case 6: Invalid - p below minimum
void test_case_6() {
    int result = simple(4999, 3, 10);
    // Frama-C should flag this
}

// Test case 7: Invalid - n at zero
void test_case_7() {
    int result = simple(5000, 0, 5);
    // Frama-C should flag this
}

// Test case 8: Valid - Large p value within INT_MAX constraint
// p=100,000; n=4; r=14. Product p*n*r = 5,600,000, which is << INT_MAX (approx 2.1B).
void test_case_8() {
    int result = simple(100000, 4, 14);
    printf("test_case_8: %d\n", result);  // Expected: 56000
}

// Test case 9: Valid - Extreme upper boundary of n and r
// p=5000; n=4 (max < 5); r=14 (max < 15).
void test_case_9() {
    int result = simple(5000, 4, 14);
    printf("test_case_9: %d\n", result);  // Expected: 2800
}

// Harness entry point
void test_harness_simple() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and 7 intentionally not called - for precondition testing
}