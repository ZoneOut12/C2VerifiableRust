// ========== Original Code (with ACSL) ==========
#include <assert.h>
#include <limits.h>
/*
 * "nested4.c" from InvGen benchmark suite
 */

/*@
  requires l > 0;
  requires n > l;
*/
void foo(int n, int l) {
  int i,k;

  /*@
  loop invariant 1 <= k <= n;
  loop assigns k;
  loop assigns i;
  loop variant n - k;
  */
  for (k=1; k<n; k++){
    /*@
    loop invariant l <= i <= n;
    loop assigns i;
    loop variant n - i;
    */
    for (i=l; i<n; i++) {
    }
    /*@
    loop invariant l <= i <= n;
    loop assigns i;
    loop variant n - i;
    */
    for (i=l; i<n; i++) {
      //@ assert 1<=i;
    }
  }

}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - n=5, l=2
void test_case_1() {
    foo(5, 2);
    printf("test_case_1: passed\n");
}

// Test case 2: Valid - n=10, l=1
void test_case_2() {
    foo(10, 1);
    printf("test_case_2: passed\n");
}

// Test case 3: Valid - n=3, l=1
void test_case_3() {
    foo(3, 1);
    printf("test_case_3: passed\n");
}

// Test case 4: Valid - n=100, l=50
void test_case_4() {
    foo(100, 50);
    printf("test_case_4: passed\n");
}

// Test case 5: Valid - n=4, l=1
void test_case_5() {
    foo(4, 1);
    printf("test_case_5: passed\n");
}

// Test case 6: Invalid - l=0 (violates l > 0)
void test_case_6() {
    foo(5, 0);  // Frama-C should flag this
}

// Test case 7: Invalid - n=2 <= l=3 (violates n > l)
void test_case_7() {
    foo(2, 3);  // Frama-C should flag this
}

// Test case 8: Boundary - n=2, l=1 (minimum allowed)
void test_case_8() {
    foo(2, 1);
    printf("test_case_8: passed\n");
}

// Test case 9: Boundary - n=10, l=9
void test_case_9() {
    foo(10, 9);
    printf("test_case_9: passed\n");
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