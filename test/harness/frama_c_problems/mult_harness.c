/*@ requires a >= 0 && b >= 0;
    requires a*b <= INT_MAX;
    ensures \result == a*b;
    assigns \nothing;
*/
int mul(int a, int b) {
    int x = a, prod = 0;
    /*@ 
        loop invariant x >= 0;
        loop invariant prod == (a-x)*b;
        loop assigns prod, x;
        loop variant x;
    */
    while(x > 0) {
        //@ assert x >= 1 && prod == (a-x)*b;
        //@ assert prod <= a*b - b;
        prod = prod + b;
        x--;
    }
    return prod;
}

// ========== Test Cases ==========
#include <stdio.h>
#include <limits.h>

// Test case 1: Valid - normal case
void test_case_1() {
    int result = mul(2, 5);
    printf("test_case_1: %d\n", result);  // Expected: 10
}

// Test case 2: Valid - zero first parameter
void test_case_2() {
    int result = mul(0, 5);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - zero second parameter
void test_case_3() {
    int result = mul(5, 0);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - larger values
void test_case_4() {
    int result = mul(10, 100);
    printf("test_case_4: %d\n", result);  // Expected: 1000
}

// Test case 5: Valid - product equals INT_MAX
void test_case_5() {
    int result = mul(1, INT_MAX);
    printf("test_case_5: %d\n", result);  // Expected: INT_MAX
}

// Test case 6: Invalid - negative first parameter
void test_case_6() {
    int result = mul(-1, 5);
    // No output check
}

// Test case 7: Invalid - product exceeds INT_MAX
void test_case_7() {
    int result = mul(1073741824, 2);
    // No output check
}

// Test case 8: Boundary - both zeros
void test_case_8() {
    int result = mul(0, 0);
    printf("test_case_8: %d\n", result);  // Expected: 0
}

// Test case 9: Boundary - product at maximum
void test_case_9() {
    int result = mul(INT_MAX, 1);
    printf("test_case_9: %d\n", result);  // Expected: INT_MAX
}

void test_harness_mul() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // Invalid cases not called
}