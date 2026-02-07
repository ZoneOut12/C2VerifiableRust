// ========== Original Code (with ACSL) ==========
int main(){
  int i = 0;
  int h = 42;
  
  /*@
    loop invariant 0 <= i <= 30;
    loop assigns i;
    loop variant 30 - i;
  */
  while(i < 30){
    ++i;
  }
  //@assert i == 30;
  //@assert h == 42;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal execution
void test_case_1() {
    main();
    printf("test_case_1: executed main\n");
}

// Test case 2: Valid - repeated execution
void test_case_2() {
    main();
    printf("test_case_2: executed main\n");
}

// Test case 3: Valid - standard environment
void test_case_3() {
    main();
    printf("test_case_3: executed main\n");
}

// Test case 4: Valid - no external interference
void test_case_4() {
    main();
    printf("test_case_4: executed main\n");
}

// Test case 5: Valid - default stack alignment
void test_case_5() {
    main();
    printf("test_case_5: executed main\n");
}

// Test case 6: Invalid - no preconditions to violate
void test_case_6() {
    main();
    // Frama-C should not flag this as invalid
}

// Test case 7: Invalid - no preconditions to violate
void test_case_7() {
    main();
    // Frama-C should not flag this as invalid
}

// Test case 8: Boundary - loop termination
void test_case_8() {
    main();
    printf("test_case_8: executed main\n");
}

// Test case 9: Boundary - initial i value
void test_case_9() {
    main();
    printf("test_case_9: executed main\n");
}

// Harness entry point (not main!)
void test_harness_main() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // test_case_6 and 7 intentionally not called - they're for precondition testing
    test_case_8();
    test_case_9();
}
int test_case_1() {
    int result = main();
    assert(result == 0);
    return 0;
}

int test_case_2() {
    int result = main();
    assert(result == 0);
    return 0;
}

int test_case_3() {
    int result = main();
    assert(result == 0);
    return 0;
}

int test_case_4() {
    int result = main();
    assert(result == 0);
    return 0;
}

int test_case_5() {
    int result = main();
    assert(result == 0);
    return 0;
}

int test_case_6() {
    int result = main();
    assert(result == 1);
    return 0;
}

int test_case_7() {
    int result = main();
    assert(result == 255);
    return 0;
}

int test_case_8() {
    int result = main();
    assert(result == 0);
    return 0;
}

int test_case_9() {
    int result = main();
    assert(result == 255);
    return 0;
}