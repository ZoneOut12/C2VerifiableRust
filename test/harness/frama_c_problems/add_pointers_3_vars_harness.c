// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@
    requires \valid_read(a) && \valid_read(b) && \valid_read(r);
    requires \separated(a, b, r);
    requires *a + *b <= INT_MAX;
    requires *a + *b >= INT_MIN;
    requires *a + *b + *r <= INT_MAX;
    requires *a + *b + *r >= INT_MIN;
    assigns \nothing;
    ensures \result == *a + *b + *r;
*/
int add(int *a, int *b, int *r) {
    return *a + *b + *r;
}

int main() {
    int a = 24;
    int b = 32;
    int r = 12;
    int x;
    x = add(&a, &b, &r) ;
    //@ assert x == a + b + r;
    //@ assert x == 68 ;

}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal case
void test_case_1() {
    int a = 24;
    int b = 32;
    int r = 12;
    int result = add(&a, &b, &r);
    printf("test_case_1: %d\n", result); // Expected 68
}

// Test case 2: Valid - sum a+b is INT_MAX-1
void test_case_2() {
    int a = INT_MAX - 2;
    int b = 1;
    int r = 1;
    int result = add(&a, &b, &r);
    printf("test_case_2: %d\n", result); // Expected INT_MAX
}

// Test case 3: Valid - negative values
void test_case_3() {
    int a = -10;
    int b = -20;
    int r = -30;
    int result = add(&a, &b, &r);
    printf("test_case_3: %d\n", result); // Expected -60
}

// Test case 4: Valid - all zeros
void test_case_4() {
    int a = 0;
    int b = 0;
    int r = 0;
    int result = add(&a, &b, &r);
    printf("test_case_4: %d\n", result); // Expected 0
}

// Test case 5: Valid - sum a+b is INT_MIN
void test_case_5() {
    int a = -1073741824;
    int b = -1073741824;
    int r = 1;
    int result = add(&a, &b, &r);
    printf("test_case_5: %d\n", result); // Expected -2147483647
}

// Test case 6: Boundary - sum is INT_MAX
void test_case_6() {
    int a = INT_MAX;
    int b = 0;
    int r = 0;
    int result = add(&a, &b, &r);
    printf("test_case_6: %d\n", result); // Expected INT_MAX
}

// Test case 7: Boundary - sum is INT_MIN
void test_case_7() {
    int a = INT_MIN;
    int b = 0;
    int r = 0;
    int result = add(&a, &b, &r);
    printf("test_case_7: %d\n", result); // Expected INT_MIN
}

// Test case 8: Invalid - a and b point to same variable
void test_case_8() {
    int a = INT_MAX - 1;
    int b = INT_MAX - 1;
    int r = INT_MAX - 1;
    int result = add(&a, &b, &r);
    // Frama-C should flag this
}

// Test case 9: Invalid - a + b overflows
void test_case_9() {
    int a = INT_MAX;
    int b = 1;
    int r = 0;
    int result = add(&a, &b, &r);
    // Frama-C should flag this
}

// Harness entry point
void test_harness_add() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // Invalid test cases are not called to avoid runtime errors
}