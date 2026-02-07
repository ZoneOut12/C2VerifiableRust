// ========== Original Code (with ACSL) ==========
void foo(){
  int x = -20 ;

  /*@
    loop variant -x ;
  */
  while(x < 0){
    x += 4 ;
  }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal execution
void test_case_1() {
    foo();  // Expected: Loop completes normally
}

// Test case 2: Valid - redundant execution
void test_case_2() {
    foo();  // Expected: Same behavior as test_case_1
}

// Test case 3: Valid - additional execution
void test_case_3() {
    foo();  // Expected: Loop completes normally
}

// Test case 4: Valid - repeated execution
void test_case_4() {
    foo();  // Expected: Loop completes normally
}

// Test case 5: Valid - final repetition
void test_case_5() {
    foo();  // Expected: Loop completes normally
}

// Test case 6: Invalid - no preconditions to violate
void test_case_6() {
    foo();  // Expected: No precondition violation possible
}

// Test case 7: Invalid - no preconditions to violate
void test_case_7() {
    foo();  // Expected: No precondition violation possible
}

// Test case 8: Boundary - loop variant reaches zero
void test_case_8() {
    foo();  // Expected: Loop completes with x == 0
}

// Test case 9: Boundary - loop terminates cleanly
void test_case_9() {
    foo();  // Expected: Loop completes normally
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
    test_case_8();
    test_case_9();
}
void test_case_6() {
    foo();
    // Add assertions here based on foo's expected side effects
}

void test_case_7() {
    foo();
    // Add assertions here based on foo's expected side effects
}