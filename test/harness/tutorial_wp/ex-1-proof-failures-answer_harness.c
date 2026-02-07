// ========== Original Code (with ACSL) ==========
#include <limits.h>

/*@ requires x > INT_MIN ;
    assigns \nothing ;
    ensures x >= 0 ==> \result == x ;
    ensures x <  0 ==> \result == -x ; */
int abs(int x){
  return x >= 0 ? x : -x ;
}

/*@ requires INT_MIN < b - a <= INT_MAX;
    assigns \nothing ;
    ensures a < b  ==> a + \result == b ;
    ensures b <= a ==> a - \result == b ; */
int distance(int a, int b){
  return abs(b - a) ;
}

/*@ 
  requires a < b  ==> b - a <= INT_MAX ;
  requires b <= a ==> a - b <= INT_MAX ;

  assigns \nothing ;

  ensures a < b  ==> a + \result == b ;
  ensures b <= a ==> a - \result == b ;
*/
int old_distance(int a, int b){
  if(a < b) return b - a ;
  else return a - b ;
}

extern int old;
extern int new;

/*@ requires INT_MIN < b - a <= INT_MAX; */
void test(int a, int b){
  old = old_distance(a, b);
  new = distance(a, b);
  // assert old == new ;
}

// ========== Test Cases ==========
#include <stdio.h>

int old;
int new;

// Test case 1: Valid - normal positive difference
void test_case_1() {
    test(5, 10);
    printf("test_case_1: old=%d, new=%d\n", old, new);
}

// Test case 2: Valid - positive difference with negative a
void test_case_2() {
    test(-5, 3);
    printf("test_case_2: old=%d, new=%d\n", old, new);
}

// Test case 3: Valid - large difference
void test_case_3() {
    test(-1000000, 1000000);
    printf("test_case_3: old=%d, new=%d\n", old, new);
}

// Test case 4: Valid - minimal positive difference
void test_case_4() {
    test(0, 1);
    printf("test_case_4: old=%d, new=%d\n", old, new);
}

// Test case 5: Valid - negative difference
void test_case_5() {
    test(100, -50);
    printf("test_case_5: old=%d, new=%d\n", old, new);
}

// Test case 6: Invalid - b - a equals INT_MIN
void test_case_6() {
    test(0, -2147483648);
}

// Test case 7: Invalid - b - a exceeds INT_MAX
void test_case_7() {
    test(-2147483648, 2147483647);
}

// Test case 8: Boundary - b - a equals INT_MIN + 1
void test_case_8() {
    test(0, -2147483647);
    printf("test_case_8: old=%d, new=%d\n", old, new);
}

// Test case 9: Boundary - b - a equals INT_MAX
void test_case_9() {
    test(0, 2147483647);
    printf("test_case_9: old=%d, new=%d\n", old, new);
}

// Harness entry point (not main!)
void test_harness_test() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and 7 intentionally not called
}

// --- Valid Test Cases ---
void test_abs_valid() {
    // L1: Positive integer
    printf("abs_L1: %d\n", abs(10));       // Expected: 10
    // L2: Negative integer
    printf("abs_L2: %d\n", abs(-5));       // Expected: 5
    // L3: Zero boundary
    printf("abs_L3: %d\n", abs(0));        // Expected: 0
    // L4: Maximum positive integer
    printf("abs_L4: %d\n", abs(INT_MAX));  // Expected: 2147483647
    // L5: Smallest valid negative integer
    printf("abs_L5: %d\n", abs(INT_MIN + 1)); // Expected: 2147483647
    // L6: Positive one
    printf("abs_L6: %d\n", abs(1));        // Expected: 1
    // L7: Negative one
    printf("abs_L7: %d\n", abs(-1));       // Expected: 1
}

// --- Invalid Test Cases ---
void test_abs_invalid() {
    // L8: Violates x > INT_MIN (Negating INT_MIN causes overflow)
    abs(INT_MIN); 
    // L9: Extreme underflow (Redundant but consistent)
    abs(INT_MIN);
}

// --- Valid Test Cases ---
void test_distance_valid() {
    // L1: a < b
    printf("dist_L1: %d\n", distance(10, 20));   // Expected: 10
    // L2: b < a
    printf("dist_L2: %d\n", distance(20, 10));   // Expected: 10
    // L3: Same values
    printf("dist_L3: %d\n", distance(5, 5));     // Expected: 0
    // L4: Negative to Positive
    printf("dist_L4: %d\n", distance(-5, 5));    // Expected: 10
    // L5: Large positive range
    printf("dist_L5: %d\n", distance(0, INT_MAX)); // Expected: 2147483647
    // L6: Minimum difference
    printf("dist_L6: %d\n", distance(100, 101)); // Expected: 1
    // L7: Both negative
    printf("dist_L7: %d\n", distance(-10, -2));  // Expected: 8
}

// --- Invalid Test Cases ---
void test_distance_invalid() {
    // L8: Violates INT_MIN < b - a (Result is exactly INT_MIN)
    distance(1, INT_MIN); 
    // L9: Violates b - a <= INT_MAX (Overflowing distance)
    distance(INT_MAX, -10); 
}

// --- Valid Test Cases ---
void test_old_distance_valid() {
    // L1: Standard a < b
    printf("old_dist_L1: %d\n", old_distance(0, 100));   // Expected: 100
    // L2: Standard b < a
    printf("old_dist_L2: %d\n", old_distance(100, 0));   // Expected: 100
    // L3: Zero values
    printf("old_dist_L3: %d\n", old_distance(0, 0));     // Expected: 0
    // L4: Max distance a < b
    printf("old_dist_L4: %d\n", old_distance(0, INT_MAX)); // Expected: 2147483647
    // L5: Max distance b < a
    printf("old_dist_L5: %d\n", old_distance(INT_MAX, 0)); // Expected: 2147483647
    // L6: Negative boundary
    printf("old_dist_L6: %d\n", old_distance(-1, 0));    // Expected: 1
    // L7: Both negative
    printf("old_dist_L7: %d\n", old_distance(-50, -20)); // Expected: 30
}

// --- Invalid Test Cases ---
void test_old_distance_invalid() {
    // L8: Violates b - a <= INT_MAX (Resulting distance too large)
    old_distance(INT_MIN, 1);
    // L9: Violates a - b <= INT_MAX
    old_distance(1, INT_MIN);
}