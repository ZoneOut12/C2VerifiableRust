// ========== Original Code (with ACSL) ==========
#include "assert.h"

# define LARGE_INT 10

/*@ 
requires 0 <= k && k <= 1;
*/
int foo(int k) {
    int i,j;
    i = 1;
    int tmp = k;
    /*@
    loop invariant i == k + 2 * (i - 1) || i== k + 1 + 2 * (i - 1);
    loop invariant i + k <= 2;
    loop invariant 1 <= i;
    loop invariant 1 <= i + k;
    loop assigns k;
    loop assigns j;
    loop assigns i;
    loop variant LARGE_INT - i;
    */
    while (i < LARGE_INT) {
        i = i + 1;
        k = k - 1;
        //@ assert 1 <= i + k && i + k <= 2 && i >= 1;
    }
    return 0;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid input k=0
void test_case_1() {
    int result = foo(0);
    printf("test_case_1: %d\n", result);  // Expected: 0
}

// Test case 2: Valid input k=1
void test_case_2() {
    int result = foo(1);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Invalid input k=-1
void test_case_3() {
    int result = foo(-1);  // Frama-C should flag this
}

// Test case 4: Invalid input k=2
void test_case_4() {
    int result = foo(2);  // Frama-C should flag this
}

// Test case 5: Boundary input k=0
void test_case_5() {
    int result = foo(0);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary input k=1
void test_case_6() {
    int result = foo(1);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Harness entry point (not main!)
void test_harness_foo() {
    test_case_1();
    test_case_2();
    test_case_5();
    test_case_6();
    // test_case_3 and test_case_4 intentionally not called - for precondition testing
}
void test_case_3() {
    int result = foo(-1);
    assert(result == -1);
}

void test_case_4() {
    int result = foo(2);
    assert(result == -1);
}