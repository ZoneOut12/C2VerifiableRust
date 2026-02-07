// ========== Original Code (with ACSL) ==========
/*@ inductive even_natural(integer n) {
  case even_nul:
    even_natural(0);
  case even_not_nul_natural:
    \forall integer n ;
      even_natural(n) ==> even_natural(n+2);
  case odd_case_0:
      !even_natural(1);
  case odd_case_n:
    \forall integer n ;
      !even_natural(n) ==> !even_natural(n+2);
  }
*/

/*@ requires even_natural(n);
    assigns \nothing;
*/
void check_even(int n) {
  //@ assert even_natural(n);
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - zero
void test_case_1() {
  check_even(0);
  printf("test_case_1: SUCCESS\n");
}

// Test case 2: Valid - minimal even
void test_case_2() {
  check_even(2);
  printf("test_case_2: SUCCESS\n");
}

// Test case 3: Valid - large even
void test_case_3() {
  check_even(42);
  printf("test_case_3: SUCCESS\n");
}

// Test case 4: Boundary - zero
void test_case_4() {
  check_even(0);
  printf("test_case_4: SUCCESS\n");
}

// Test case 5: Boundary - first even after zero
void test_case_5() {
  check_even(2);
  printf("test_case_5: SUCCESS\n");
}

// Test case 6: Invalid - smallest odd
void test_case_6() {
  check_even(1);  // Frama-C should flag this
}

// Test case 7: Invalid - odd number
void test_case_7() {
  check_even(3);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_check_even() {
  test_case_1();
  test_case_2();
  test_case_3();
  test_case_4();
  test_case_5();
  // Invalid test cases intentionally not called - for precondition testing
}
void test_case_6() {
    check_even(4);
}

void test_case_7() {
    check_even(-2);
}