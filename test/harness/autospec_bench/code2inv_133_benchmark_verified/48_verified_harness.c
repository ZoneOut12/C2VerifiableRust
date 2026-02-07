// ========== Original Code (with ACSL) ==========
int unknown() {
    return 0;
}

/*@ requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c == n ==> \forall integer k; 0 <= k < c ==> k != n;
  loop invariant c != n || c <= n;
  loop invariant 0 <= c;
  loop invariant (c == n) ==> (n > -1);
  loop assigns n;
  loop assigns c;
  */
  while (unknown()) {
      if(unknown()) {
        if(c != n) {
          if (c >= 2147483647) break;
          (c = (c + 1));
        }
      } else {
        if (c == n) {
          c = 1;
        }
      }
  }
  if(c == n) {
    //@ assert n > -1;
  }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - n=5
void test_case_1() {
    foo(5);
    printf("test_case_1 executed\\n");
}

// Test case 2: Valid - n=10
void test_case_2() {
    foo(10);
    printf("test_case_2 executed\\n");
}

// Test case 3: Valid - n=42
void test_case_3() {
    foo(42);
    printf("test_case_3 executed\\n");
}

// Test case 4: Valid - n=100
void test_case_4() {
    foo(100);
    printf("test_case_4 executed\\n");
}

// Test case 5: Valid - n=1000
void test_case_5() {
    foo(1000);
    printf("test_case_5 executed\\n");
}

// Test case 6: Invalid - n=0
void test_case_6() {
    foo(0);
}

// Test case 7: Invalid - n=-5
void test_case_7() {
    foo(-5);
}

// Test case 8: Boundary - n=1
void test_case_8() {
    foo(1);
    printf("test_case_8 executed\\n");
}

// Test case 9: Boundary - n=2147483647
void test_case_9() {
    foo(2147483647);
    printf("test_case_9 executed\\n");
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
    // Invalid test cases not called for execution
}
void test_case_6() {
    foo(0);
}

void test_case_7() {
    foo(-5);
}