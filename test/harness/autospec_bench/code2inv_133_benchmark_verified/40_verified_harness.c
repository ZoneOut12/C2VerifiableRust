// ========== Original Code (with ACSL) ==========
int unknown();

/*@ requires n > 0; */
void foo(int n) {
  int c = 0;

  /*@
  loop invariant c <= n;
  loop invariant c <= n || c == 1;
  loop invariant 0 <= c;
  loop invariant (c <= n && c >= 0) || (c == n+1);
  loop assigns c;
  */
  while (unknown()) {
    if (unknown()) {
      if (c > n) {
        c  = c + 1;
      }
    } else {
      if (c == n) {
        c  = 1;
      }
    }
  }
  if ( (c != n) ) {
    //@ assert  (c >= 0) ;
  }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - n=3
void test_case_1() {
    foo(3);
    printf("test_case_1: foo called with n=3\\n");
}

// Test case 2: Valid - n=5
void test_case_2() {
    foo(5);
    printf("test_case_2: foo called with n=5\\n");
}

// Test case 3: Valid - n=7
void test_case_3() {
    foo(7);
    printf("test_case_3: foo called with n=7\\n");
}

// Test case 4: Valid - n=2 (also boundary)
void test_case_4() {
    foo(2);
    printf("test_case_4: foo called with n=2\\n");
}

// Test case 5: Valid - n=10
void test_case_5() {
    foo(10);
    printf("test_case_5: foo called with n=10\\n");
}

// Test case 6: Boundary - n=1
void test_case_6() {
    foo(1);
    printf("test_case_6: foo called with n=1\\n");
}

// Test case 7: Boundary - n=2
void test_case_7() {
    foo(2);
    printf("test_case_7: foo called with n=2\\n");
}

// Test case 8: Invalid - n=0
void test_case_8() {
    foo(0);
    // Frama-C should flag this
}

// Test case 9: Invalid - n=-3
void test_case_9() {
    foo(-3);
    // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_foo() {
    // Valid cases
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // Boundary cases
    test_case_6();
    test_case_7();
    // Invalid cases are defined but not called
}
void test_case_1() { foo(5); }
void test_case_2() { foo(10); }
void test_case_3() { foo(2); }
void test_case_4() { foo(3); }
void test_case_5() { foo(7); }
void test_case_6() { foo(1); }
void test_case_7() { foo(1000000); }
void test_case_8() { foo(0); }
void test_case_9() { foo(-1); }