// ========== Original Code (with ACSL) ==========
//@ ghost int x ;

/*@ ghost
  /@ assigns x ; @/
  void ghost_foo(void);
*/

/*@ assigns x; */
void foo(void){
  /*@ ghost
    /@ loop assigns x, i; @/
    for(int i = 0; i < 10; ++i);
  */
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - basic call
void test_case_1() {
    foo();
    printf("test_case_1: foo executed successfully\n");
}

// Test case 2: Valid - second invocation
void test_case_2() {
    foo();
    printf("test_case_2: foo executed successfully\n");
}

// Test case 3: Valid - third execution
void test_case_3() {
    foo();
    printf("test_case_3: foo executed successfully\n");
}

// Test case 4: Valid - fourth call
void test_case_4() {
    foo();
    printf("test_case_4: foo executed successfully\n");
}

// Test case 5: Valid - fifth execution
void test_case_5() {
    foo();
    printf("test_case_5: foo executed successfully\n");
}

// Test case 6: Invalid - no preconditions to violate
void test_case_6() {
    foo();  // No precondition violation possible
}

// Test case 7: Invalid - no preconditions to violate
void test_case_7() {
    foo();  // No precondition violation possible
}

// Test case 8: Boundary - minimal execution
void test_case_8() {
    foo();
    printf("test_case_8: foo executed successfully\n");
}

// Test case 9: Boundary - edge scenario
void test_case_9() {
    foo();
    printf("test_case_9: foo executed successfully\n");
}

// Harness entry point (not main!)
void test_harness_foo() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // test_case_6 and 7 intentionally not called - for precondition testing
    test_case_8();
    test_case_9();
}
void test_case_6() {
    foo();
}

void test_case_7() {
    foo();
}