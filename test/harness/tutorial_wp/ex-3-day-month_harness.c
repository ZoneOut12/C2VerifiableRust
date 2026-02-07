// ========== Original Code (with ACSL) ==========
/*@
  requires 1 <= m <= 12 ;
  ensures m \in { 2 } ==> \result == 28 ;
  ensures m \in { 1, 3, 5, 7, 8, 10, 12 } ==> \result == 31 ;
  ensures m \in { 4, 6, 9, 11 } ==> \result == 30 ;
*/
int day_of(int m){
  int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 } ;
  return days[m-1] ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - February has 28 days
void test_case_1() {
    int result = day_of(2);
    printf("test_case_1: %d\n", result);  // Expected: 28
}

// Test case 2: Valid - March has 31 days
void test_case_2() {
    int result = day_of(3);
    printf("test_case_2: %d\n", result);  // Expected: 31
}

// Test case 3: Valid - April has 30 days
void test_case_3() {
    int result = day_of(4);
    printf("test_case_3: %d\n", result);  // Expected: 30
}

// Test case 4: Valid - July has 31 days
void test_case_4() {
    int result = day_of(7);
    printf("test_case_4: %d\n", result);  // Expected: 31
}

// Test case 5: Valid - September has 30 days
void test_case_5() {
    int result = day_of(9);
    printf("test_case_5: %d\n", result);  // Expected: 30
}

// Test case 6: Invalid - m less than lower bound
void test_case_6() {
    int result = day_of(0);  // Frama-C should flag this
}

// Test case 7: Invalid - m greater than upper bound
void test_case_7() {
    int result = day_of(13);  // Frama-C should flag this
}

// Test case 8: Boundary - first month (lower bound)
void test_case_8() {
    int result = day_of(1);
    printf("test_case_8: %d\n", result);  // Expected: 31
}

// Test case 9: Boundary - twelfth month (upper bound)
void test_case_9() {
    int result = day_of(12);
    printf("test_case_9: %d\n", result);  // Expected: 31
}

// Harness entry point (not main!)
void test_harness_day_of() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // Invalid test cases (6 and 7) are not called
}
void test_case_6() {
    int result = day_of(0);
    assert(result == -1);
}
void test_case_7() {
    int result = day_of(13);
    assert(result == -1);
}