// ========== Original Code (with ACSL) ==========
/*@ requires n > 0;
*/
void foo(int n)
{
    int x = 0;
    int m = 0;

    /*@
    loop invariant x <= n;
    loop invariant n > 0 ==> m >= 0;
    loop invariant n > 0 ==> m < n;
    loop invariant m <= x;
    loop invariant 0 <= x;
    loop assigns x;
    loop assigns m;
    loop variant n - x;
    */
    while (x < n) {
        if (unknown()) {
            m = x;
        }
        x = x + 1;
    }

    if(n > 0) {
       //@ assert m < n;
       //@ assert m >= 0;
    }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - n=5
void test_case_1() {
    foo(5);
    printf("test_case_1: completed\n");
}

// Test case 2: Valid - n=3
void test_case_2() {
    foo(3);
    printf("test_case_2: completed\n");
}

// Test case 3: Valid - n=7
void test_case_3() {
    foo(7);
    printf("test_case_3: completed\n");
}

// Test case 4: Valid - n=10
void test_case_4() {
    foo(10);
    printf("test_case_4: completed\n");
}

// Test case 5: Valid - n=4
void test_case_5() {
    foo(4);
    printf("test_case_5: completed\n");
}

// Test case 6: Invalid - n=0 (violates n > 0)
void test_case_6() {
    foo(0);  // Frama-C should flag this
}

// Test case 7: Invalid - n=-2 (violates n > 0)
void test_case_7() {
    foo(-2);  // Frama-C should flag this
}

// Test case 8: Boundary - n=1
void test_case_8() {
    foo(1);
    printf("test_case_8: completed\n");
}

// Test case 9: Boundary - n=2
void test_case_9() {
    foo(2);
    printf("test_case_9: completed\n");
}

// Harness entry point (not main!)
void test_harness_foo() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called - for precondition testing
}
void test_case_1() { foo(5); }
void test_case_2() { foo(10); }
void test_case_3() { foo(2); }
void test_case_4() { foo(100); }
void test_case_5() { foo(3); }
void test_case_6() { foo(0); }
void test_case_7() { foo(-4); }
void test_case_8() { foo(1); }
void test_case_9() { foo(2147483647); }