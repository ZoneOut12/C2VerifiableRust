// ========== Original Code (with ACSL) ==========
int unknown();

/*@ requires n > 0;
*/
void foo(int n) {
    int c = 0;

    /*@
    loop invariant c <= n;
    loop invariant 0 <= c;
    loop invariant (c == n) ==> (c >= 0 && c <= n);
    loop assigns c;
    */
    while (unknown()) {
        if(c == n) {
            c = 1;
        }
        else {
            c = c + 1;
        }
    }

    if(c == n) {
        //@ assert  c >= 0;
    }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - n=5
void test_case_1() {
    foo(5);
}

// Test case 2: Valid - n=3
void test_case_2() {
    foo(3);
}

// Test case 3: Valid - n=2
void test_case_3() {
    foo(2);
}

// Test case 4: Valid - n=10
void test_case_4() {
    foo(10);
}

// Test case 5: Valid - n=7
void test_case_5() {
    foo(7);
}

// Test case 6: Invalid - n=0 (violates n > 0)
void test_case_6() {
    foo(0);
}

// Test case 7: Invalid - n=-3 (violates n > 0)
void test_case_7() {
    foo(-3);
}

// Test case 8: Boundary - n=1 (minimum valid)
void test_case_8() {
    foo(1);
}

// Test case 9: Boundary - n=2
void test_case_9() {
    foo(2);
}

// Harness entry point
void test_harness_foo() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // Invalid test cases (6 and 7) intentionally not called
}
void test_case_1() { foo(5); }
void test_case_2() { foo(10); }
void test_case_3() { foo(3); }
void test_case_4() { foo(1); }
void test_case_5() { foo(100); }
void test_case_6() { foo(0); }
void test_case_7() { foo(-5); }
void test_case_8() { foo(1); }
void test_case_9() { foo(0); }