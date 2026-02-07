// ========== Original Code (with ACSL) ==========
int unknown();

/*@
requires x == y;
*/
void foo(int x, int y) {
  int lock = 1;
  
  /*@
  loop invariant x == y;
  loop invariant lock == 1;
  loop invariant lock == 1 || lock == 0;
  loop invariant lock == 0 || lock == 1;
  loop invariant lock != 1 ==> x == y;
  loop invariant (lock == 1) || (lock == 0);
  loop assigns y;
  loop assigns x;
  loop assigns lock;
  */
  while (x != y) {  
    if (unknown()) {
      lock = 1;
      x = y;
    } else {
      lock  = 0;
      x  = y;
      y  = y + 1; 
    }
  }
  //@ assert lock == 1;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - x = 5, y = 5
void test_case_1() {
    foo(5, 5);
}

// Test case 2: Valid - x = 10, y = 10
void test_case_2() {
    foo(10, 10);
}

// Test case 3: Valid - x = -3, y = -3
void test_case_3() {
    foo(-3, -3);
}

// Test case 4: Valid - x = 100, y = 100
void test_case_4() {
    foo(100, 100);
}

// Test case 5: Valid - x = 42, y = 42
void test_case_5() {
    foo(42, 42);
}

// Test case 6: Boundary - x = 0, y = 0
void test_case_6() {
    foo(0, 0);
}

// Test case 7: Boundary - x = 1, y = 1
void test_case_7() {
    foo(1, 1);
}

// Test case 8: Invalid - x = 2, y = 3 (x < y)
void test_case_8() {
    foo(2, 3);
}

// Test case 9: Invalid - x = 5, y = 4 (x > y)
void test_case_9() {
    foo(5, 4);
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
    // test_case_8 and test_case_9 intentionally not called for precondition testing
}
void test_case_1() { foo(5, 5); }
void test_case_2() { foo(0, 0); }
void test_case_3() { foo(-3, -3); }
void test_case_4() { foo(2147483647, 2147483647); }
void test_case_5() { foo(-2147483648, -2147483648); }
void test_case_6() { foo(2, 3); }
void test_case_7() { foo(5, 4); }
void test_case_8() { foo(1, 1); }
void test_case_9() { foo(-1, -1); }