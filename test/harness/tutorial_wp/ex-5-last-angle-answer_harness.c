// ========== Original Code (with ACSL) ==========
/*@\
  requires 0 <= first <= 180 ;\
  requires 0 <= second <= 180 ;\
  requires first + second <= 180 ;\
\
  ensures 180 == first + second + \\result ;\
  ensures 0 <= \\result <= 180 ;
*/
int last_angle(int first, int second){
  return 180 - first - second ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal values
void test_case_1() {
    int result = last_angle(60, 60);
    printf("test_case_1: %d\n", result);  // Expected: 60
}

// Test case 2: Valid - minimum values
void test_case_2() {
    int result = last_angle(0, 0);
    printf("test_case_2: %d\n", result);  // Expected: 180
}

// Test case 3: Valid - asymmetric angles
void test_case_3() {
    int result = last_angle(90, 45);
    printf("test_case_3: %d\n", result);  // Expected: 45
}

// Test case 4: Valid - maximum first angle
void test_case_4() {
    int result = last_angle(180, 0);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid - sum exactly 180
void test_case_5() {
    int result = last_angle(100, 80);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary - zero and maximum second
void test_case_6() {
    int result = last_angle(0, 180);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary - two right angles
void test_case_7() {
    int result = last_angle(90, 90);
    printf("test_case_7: %d\n", result);  // Expected: 0
}

// Test case 8: Invalid - negative first value
void test_case_8() {
    int result = last_angle(-10, 50);  // Frama-C should flag this
}

// Test case 9: Invalid - sum exceeds 180
void test_case_9() {
    int result = last_angle(170, 20);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_last_angle() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}
void test_case_8() { run_test(test_case_8, -5, 30, 0); }
void test_case_9() { run_test(test_case_9, 170, 15, 0); }