// ========== Original Code (with ACSL) ==========
#include<limits.h>

int unknown();

/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  /*@
  loop invariant x == 20 ==> y != 0;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop assigns y;
  loop assigns x;
  */
  while (unknown()) {
    if (x > 2147483647 - 10 || y > 2147483647 - 10){
      break;
    }
    x  = x + 10;
    y  = y + 10;
  }
  if (x == 20) {
    //@ assert y != 0;
  }
}


#include <stdio.h>

// Test case 1: Valid - x at lower bound, y in middle
void test_case_1() {
    foo(0, 5);
}

// Test case 2: Valid - y at lower bound, x in middle
void test_case_2() {
    foo(5, 0);
}

// Test case 3: Valid - both values in middle range
void test_case_3() {
    foo(3, 7);
}

// Test case 4: Valid - x at upper bound, y in middle
void test_case_4() {
    foo(10, 5);
}

// Test case 5: Valid - y at upper bound, x in middle
void test_case_5() {
    foo(5, 10);
}

// Test case 6: Boundary - both at lower bounds
void test_case_6() {
    foo(0, 0);
}

// Test case 7: Boundary - both at upper bounds
void test_case_7() {
    foo(10, 10);
}

// Test case 8: Invalid - x violates lower bound
void test_case_8() {
    foo(-1, 5);
}

// Test case 9: Invalid - y violates upper bound
void test_case_9() {
    foo(5, 11);
}

// Harness entry point (not main!)
void test_harness_foo() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // Invalid test cases intentionally not called
}
