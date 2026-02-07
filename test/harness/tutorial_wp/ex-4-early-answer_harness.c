// ========== Original Code (with ACSL) ==========
void foo(){
  int i ;
  int x = 0 ;
  /*@
    loop invariant 0 <= i <= 19 ;
    loop assigns i ;
    loop variant 19 - i ;
  */
  for(i = 0 ; i < 20 ; ++i){
    if(i == 19){
      x++ ;
      break ;
    }
  }
  //@ assert x == 1 ;
  //@ assert i == 19 ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal execution
void test_case_1() {
    foo();
}

// Test case 2: Valid - repeated execution
void test_case_2() {
    foo();
}

// Test case 3: Valid - another instance
void test_case_3() {
    foo();
}

// Test case 4: Valid - additional valid case
void test_case_4() {
    foo();
}

// Test case 5: Valid - fifth execution
void test_case_5() {
    foo();
}

// Test case 6: Boundary - loop edge case
void test_case_6() {
    foo();
}

// Test case 7: Boundary - final iteration
void test_case_7() {
    foo();
}

// Test case 8: Invalid - no preconditions to violate
void test_case_8() {
    foo();
}

// Test case 9: Invalid - hypothetical precondition violation
void test_case_9() {
    foo();
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
    // test_case_8 and test_case_9 intentionally not called
}
void test_case_8() {
    foo();
}
void test_case_9() {
    foo();
}