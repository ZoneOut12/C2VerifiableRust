// ========== Original Code (with ACSL) ==========
/*@ 
  assigns \nothing ;
  ensures \result <==> ((y % 4 == 0) && (y % 100 !=0)) || (y % 400==0);
*/
int leap(int y){
  return ((y % 4 == 0) && (y % 100 !=0)) || (y % 400==0) ;
}

/*@
  requires 1 <= m <= 12 ;

  assigns \nothing ;

  behavior february_leap:
    assumes m \in { 2 } ;
    assumes ((y % 4 == 0) && (y % 100 !=0)) || (y % 400==0) ;
    ensures \result == 29 ;

  behavior february_not_leap:
    assumes m \in { 2 } ;
    assumes ! ( ((y % 4 == 0) && (y % 100 !=0)) || (y % 400==0) ) ;
    ensures \result == 28 ;

  behavior thirty:
    assumes m \in { 4, 6, 9, 11 } ;
    ensures \result == 30 ;

  behavior thirty_one:
    assumes m \in { 1, 3, 5, 7, 8, 10, 12 } ;
    ensures \result == 31 ;

  complete behaviors;
  disjoint behaviors;
*/
int day_of(int m, int y){
  int days[] = { 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 } ;
  int n = days[m-1] ;
  if(n == 28){
    if(leap(y)) return 29 ;
    else return 28 ;
  }
  return n ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - February in leap year
void test_case_1() {
    int result = day_of(2, 2000);
    printf("test_case_1: %d\n", result);  // Expected: 29
}

// Test case 2: Valid - February in non-leap year
void test_case_2() {
    int result = day_of(2, 1900);
    printf("test_case_2: %d\n", result);  // Expected: 28
}

// Test case 3: Valid - April (30 days)
void test_case_3() {
    int result = day_of(4, 2021);
    printf("test_case_3: %d\n", result);  // Expected: 30
}

// Test case 4: Valid - May (31 days)
void test_case_4() {
    int result = day_of(5, 2022);
    printf("test_case_4: %d\n", result);  // Expected: 31
}

// Test case 5: Valid - August (31 days)
void test_case_5() {
    int result = day_of(8, 2023);
    printf("test_case_5: %d\n", result);  // Expected: 31
}

// Test case 6: Invalid - month less than 1
void test_case_6() {
    int result = day_of(0, 2020);  // Frama-C should flag this
}

// Test case 7: Invalid - month greater than 12
void test_case_7() {
    int result = day_of(13, 2020);  // Frama-C should flag this
}

// Test case 8: Boundary - January (minimum month)
void test_case_8() {
    int result = day_of(1, 2024);
    printf("test_case_8: %d\n", result);  // Expected: 31
}

// Test case 9: Boundary - December (maximum month)
void test_case_9() {
    int result = day_of(12, 2024);
    printf("test_case_9: %d\n", result);  // Expected: 31
}

// Harness entry point
void test_harness_day_of() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called - for precondition testing
}

// ========== Additional Test Cases for leap() ==========

// Test case L1: Leap year (divisible by 4, not 100)
void test_case_leap_1() {
    int result = leap(2024);
    printf("test_case_leap_1 (2024): %d\n", result); // Expected: 1
}

// Test case L2: Leap year (divisible by 400)
void test_case_leap_2() {
    int result = leap(2000);
    printf("test_case_leap_2 (2000): %d\n", result); // Expected: 1
}

// Test case L3: Non-leap year (divisible by 100, not 400)
void test_case_leap_3() {
    int result = leap(1900);
    printf("test_case_leap_3 (1900): %d\n", result); // Expected: 0
}

// Test case L4: Non-leap year (not divisible by 4)
void test_case_leap_4() {
    int result = leap(2023);
    printf("test_case_leap_4 (2023): %d\n", result); // Expected: 0
}

// Test case L5: Boundary - Year 1 (Minimum positive year, Non-leap)
void test_case_leap_5() {
    int result = leap(1);
    printf("test_case_leap_5 (1): %d\n", result);    // Expected: 0
}

// Test case L6: Valid - Even year not divisible by 4 (Non-leap)
void test_case_leap_6() {
    int result = leap(2022);
    printf("test_case_leap_6 (2022): %d\n", result); // Expected: 0
}

// Test case L7: Valid - Large leap year (Divisible by 400)
void test_case_leap_7() {
    int result = leap(2400);
    printf("test_case_leap_7 (2400): %d\n", result); // Expected: 1
}