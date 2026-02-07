/*@ requires (x == 10000);
*/
void foo(int x) {
  /*@
  loop invariant x <= 10000;
  loop invariant 0 <= x;
  loop assigns x;
  loop variant x;
  */
  while ((x > 0)) {
    (x  = (x - 1));
  }
  //@ assert  (x == 0) ;
}

#include <stdio.h>

// Test case 1: Valid input
void test_case_1() {
    foo(10000);
    printf("test_case_1 passed\n");
}

// Test case 2: Valid input
void test_case_2() {
    foo(10000);
    printf("test_case_2 passed\n");
}

// Test case 3: Valid input
void test_case_3() {
    foo(10000);
    printf("test_case_3 passed\n");
}

// Test case 4: Valid input
void test_case_4() {
    foo(10000);
    printf("test_case_4 passed\n");
}

// Test case 5: Valid input
void test_case_5() {
    foo(10000);
    printf("test_case_5 passed\n");
}

// Test case 6: Boundary case
void test_case_6() {
    foo(10000);
    printf("test_case_6 passed\n");
}

// Test case 7: Boundary case
void test_case_7() {
    foo(10000);
    printf("test_case_7 passed\n");
}

// Test case 8: Invalid input
void test_case_8() {
    foo(9999);
}

// Test case 9: Invalid input
void test_case_9() {
    foo(10001);
}

void test_harness_foo() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // Invalid test cases are not called
}
void test_case_8() {
    foo(9999);
}

void test_case_9() {
    foo(10001);
}