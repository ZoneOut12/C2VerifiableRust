// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@
    requires \valid_read(p) && \valid_read(q);
    requires \separated(p, q);
    requires *p + *q <= INT_MAX;
    requires *p + *q >= INT_MIN;
    assigns \nothing;
    ensures \result == *p + *q;
*/
int add(int *p, int *q) {
    return *p + *q;
}

int main() {
    int a = 24;
    int b = 32;
    int x;

    x = add(&a, &b) ;
    //@ assert x == a + b ;
    //@ assert x == 56 ;


}

// ========== Test Cases ==========
#include <stdio.h>
#include <limits.h>

// Test case 1: Valid - positive numbers
void test_case_1() {
    int a = 24;
    int b = 32;
    int result = add(&a, &b);
    printf("test_case_1: %d\n", result);  // Expected: 56
}

// Test case 2: Valid - negative numbers
void test_case_2() {
    int a = -10;
    int b = -20;
    int result = add(&a, &b);
    printf("test_case_2: %d\n", result);  // Expected: -30
}

// Test case 3: Valid - mixed signs
void test_case_3() {
    int a = 50;
    int b = -20;
    int result = add(&a, &b);
    printf("test_case_3: %d\n", result);  // Expected: 30
}

// Test case 4: Valid - with zero
void test_case_4() {
    int a = 100;
    int b = 0;
    int result = add(&a, &b);
    printf("test_case_4: %d\n", result);  // Expected: 100
}

// Test case 5: Valid - zeros
void test_case_5() {
    int a = 0;
    int b = 0;
    int result = add(&a, &b);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Invalid - overlapping pointers
void test_case_6() {
    int a = INT_MIN;
    int b = INT_MIN
    int result = add(&a, &b);  // Frama-C should flag this
}

// Test case 7: Invalid - integer overflow
void test_case_7() {
    int a = INT_MAX;
    int b = 1;
    int result = add(&a, &b);  // Frama-C should flag this
}

// Test case 8: Boundary - sum equals INT_MAX
void test_case_8() {
    int a = INT_MAX;
    int b = 0;
    int result = add(&a, &b);
    printf("test_case_8: %d\n", result);  // Expected: INT_MAX
}

// Test case 9: Boundary - sum equals INT_MIN
void test_case_9() {
    int a = INT_MIN;
    int b = 0;
    int result = add(&a, &b);
    printf("test_case_9: %d\n", result);  // Expected: INT_MIN
}

// Harness entry point
void test_harness_add() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called
}
void test_case_6() {
    int q_val = 5;
    int *p = NULL;
    int res = add(p, &q_val);
}

void test_case_7() {
    int p_val = INT_MAX;
    int q_val = 1;
    int res = add(&p_val, &q_val);
}