// ========== Original Code (with ACSL) ==========
#include <limits.h>
#include "assert.h"

int unknown1() {
    return 0; // Dummy implementation
}

/*@ requires l > 0;
    requires l < INT_MAX;
    requires n < INT_MAX;
*/
void foo(int n, int l) {
    int i,k;
    /*@ loop invariant 1 <= l;
      loop invariant 1 <= k;
      loop assigns l;
      loop assigns k;
      loop assigns i;
      loop variant n - k;
    */
    for (k = 1; k < n; k++){
        /*@ loop invariant 1 <= i;
          loop assigns i;
          loop variant n - i;
        */
        for (i = l; i < n; i++){  
            //@ assert 1 <= i;
        }
        if(unknown1() && l < 2147483647) {
            l = l + 1;
        }
    }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal case
void test_case_1() {
    foo(5, 1);
    printf("test_case_1: executed\n");
}

// Test case 2: Valid - normal case
void test_case_2() {
    foo(10, 5);
    printf("test_case_2: executed\n");
}

// Test case 3: Valid - high values
void test_case_3() {
    foo(2147483640, 2147483646);
    printf("test_case_3: executed\n");
}

// Test case 4: Valid - n=-1
void test_case_4() {
    foo(-1, 1);
    printf("test_case_4: executed\n");
}

// Test case 5: Valid - negative n
void test_case_5() {
    foo(-5, 2);
    printf("test_case_5: executed\n");
}

// Test case 6: Invalid - l <= 0
void test_case_6() {
    foo(5, -5);
}

// Test case 7: Invalid - n >= INT_MAX
void test_case_7() {
    foo(INT_MAX, 1);
}

// Test case 8: Boundary - minimum values
void test_case_8() {
    foo(1, 1);
    printf("test_case_8: executed\n");
}

// Test case 9: Boundary - maximum values
void test_case_9() {
    foo(2147483646, 2147483646);
    printf("test_case_9: executed\n");
}

// Harness entry point
void test_harness_foo() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    test_case_8();
    test_case_9();
}
void test_case_6() {
    // l = 0 violates 'l > 0'
    foo(5, 0);
}

void test_case_7() {
    // n = INT_MAX violates 'n < INT_MAX'
    foo(INT_MAX, 10);
}