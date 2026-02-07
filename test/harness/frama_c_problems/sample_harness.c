// ========== Original Code (with ACSL) ==========
/*@ requires x >= 0 && y > 0;
    ensures \result == x/y;
*/
int fun(int x, int y) {
    int r = x;
    int d = 0;
    /*@ loop invariant r >= 0;
        loop invariant r + d*y == x;
        loop assigns r, d;
        loop variant r-y;
    */
    while (r >= y) {
        r = r - y;
        d = d + 1;
    }
    return d;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal division (10/2=5)
void test_case_1() {
    int result = fun(10, 2);
    printf("test_case_1: %d\n", result);
}

// Test case 2: Valid - zero dividend (0/5=0)
void test_case_2() {
    int result = fun(0, 5);
    printf("test_case_2: %d\n", result);
}

// Test case 3: Valid - dividend equals divisor (7/7=1)
void test_case_3() {
    int result = fun(7, 7);
    printf("test_case_3: %d\n", result);
}

// Test case 4: Valid - multiple subtractions (15/3=5)
void test_case_4() {
    int result = fun(15, 3);
    printf("test_case_4: %d\n", result);
}

// Test case 5: Valid - divisor is 1 (4/1=4)
void test_case_5() {
    int result = fun(4, 1);
    printf("test_case_5: %d\n", result);
}

// Test case 6: Invalid - negative dividend (-5 violates x >= 0)
void test_case_6() {
    int result = fun(-5, 3);
}

// Test case 7: Invalid - zero divisor (y=0 violates y > 0)
void test_case_7() {
    int result = fun(5, 0);
}

// Test case 8: Boundary - minimum allowed x (0/1=0)
void test_case_8() {
    int result = fun(0, 1);
    printf("test_case_8: %d\n", result);
}

// Test case 9: Boundary - dividend equals divisor (5/5=1)
void test_case_9() {
    int result = fun(5, 5);
    printf("test_case_9: %d\n", result);
}

// Harness entry point
void test_harness_fun() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called - for precondition testing
}