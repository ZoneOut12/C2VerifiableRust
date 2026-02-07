#include <limits.h>
#include "assert.h"

int __BLAST_NONDET;

/*@
requires INT_MIN < 3 * n < INT_MAX;
requires INT_MIN < m && m < INT_MAX;
requires INT_MIN < l && l < INT_MAX;
requires INT_MIN < m + l < INT_MAX;
*/
int foo(int n, int m , int l) {
    int i,j,k;
    if(3*n<=m+l); else goto END;
    /*@
    loop invariant 0 <= i;
    loop assigns k;
    loop assigns j;
    loop assigns i;
    loop variant n - i;
    */
    for (i=0;i<n;i++)
        /*@
        loop invariant i <= n;
        loop invariant 2*i <= j;
        loop invariant 0 <= i;
        loop assigns k;
        loop assigns j;
        loop variant 3 * i - j;
        */
        for (j = 2*i;j<3*i;j++)
            /*@
            loop assigns k;
            loop variant j - k;
            */
            for (k = i; k < j; k++) {
                //@ assert  k-i <= 2*n ;
            }
END:
    return 0;
}

#include <stdio.h>

// Test case 1: Valid - small positive values
void test_case_1() {
    int result = foo(1, 1, 1);
    printf("test_case_1: %d\n", result);
}

// Test case 2: Valid - moderate values
void test_case_2() {
    int result = foo(2, 3, 4);
    printf("test_case_2: %d\n", result);
}

// Test case 3: Valid - m + l = 30
void test_case_3() {
    int result = foo(10, 20, 10);
    printf("test_case_3: %d\n", result);
}

// Test case 4: Valid - n near INT_MAX/3
void test_case_4() {
    int result = foo(715827882, 0, 0);
    printf("test_case_4: %d\n", result);
}

// Test case 5: Valid - negative values
void test_case_5() {
    int result = foo(-10, -5, -5);
    printf("test_case_5: %d\n", result);
}

// Test case 6: Invalid - 3n exceeds INT_MAX
void test_case_6() {
    foo(715827883, 0, 0);
}

// Test case 7: Invalid - m + l exceeds INT_MAX
void test_case_7() {
    foo(1, 2147483646, 2);
}

// Test case 8: Boundary - 3n = INT_MAX - 1
void test_case_8() {
    int result = foo(715827882, 1, 0);
    printf("test_case_8: %d\n", result);
}

// Test case 9: Boundary - m = INT_MIN + 1
void test_case_9() {
    int result = foo(1, -2147483647, 1);
    printf("test_case_9: %d\n", result);
}

void test_harness_foo() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // test_case_6() and test_case_7() intentionally not called for invalid cases
    test_case_8();
    test_case_9();
}
int test_case_6() { return foo(INT_MAX / 3 + 1, 0, 0); }
int test_case_7() { return foo(0, INT_MAX - 1, 2); }