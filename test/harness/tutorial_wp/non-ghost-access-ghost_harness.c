// ========== Original Code (with ACSL) ==========
/*@ requires n * 42 <= INT_MAX;    
*/
int sum_42(int n){
  int x = 0 ;
  //@ ghost int r = 42 ;
  /*@
    loop invariant x == i * r;
  */
  for(int i = 0; i < n; ++i){
    x += r;
  }
  return x;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - n=1
void test_case_1() {
    int result = sum_42(1);
    printf("test_case_1: %d\n", result);  // Expected: 42
}

// Test case 2: Valid - n=10
void test_case_2() {
    int result = sum_42(10);
    printf("test_case_2: %d\n", result);  // Expected: 420
}

// Test case 3: Valid - n=100
void test_case_3() {
    int result = sum_42(100);
    printf("test_case_3: %d\n", result);  // Expected: 4200
}

// Test case 4: Valid - n=51130562
void test_case_4() {
    int result = sum_42(51130562);
    printf("test_case_4: %d\n", result);  // Expected: 2147483604
}

// Test case 5: Valid - n=2
void test_case_5() {
    int result = sum_42(2);
    printf("test_case_5: %d\n", result);  // Expected: 84
}

// Test case 6: Boundary - n=0
void test_case_6() {
    int result = sum_42(0);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary - n=51130563
void test_case_7() {
    int result = sum_42(51130563);
    printf("test_case_7: %d\n", result);  // Expected: 2147483646
}

// Test case 8: Invalid - n=51130564
void test_case_8() {
    int result = sum_42(51130564);  // Should violate precondition
}

// Test case 9: Invalid - n=100000000
void test_case_9() {
    int result = sum_42(100000000);  // Should violate precondition
}

// Harness entry point (not main!)
void test_harness_sum_42() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}