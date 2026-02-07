// ========== Original Code (with ACSL) ==========
#include <limits.h>

/*@ inductive is_gcd(integer a, integer b, integer d) {
    case gcd_zero:
      \forall integer n; is_gcd(n, 0, n);
    case gcd_succ:
      \forall integer a, b, d; 
      is_gcd(b, a % b, d) ==> is_gcd(a, b, d);
    }
*/

/*@
  requires a >= 0 && b >= 0 ;
  assigns \nothing ;
  ensures is_gcd(a, b, \result) ;
*/
unsigned gcd(unsigned a, unsigned b){
  unsigned a_pre = a;
  unsigned b_pre = b;
  /*@
    loop invariant a >= 0 && b >= 0 ;
    loop invariant \forall integer t ; is_gcd(a, b, t) ==> is_gcd(a_pre, b_pre, t) ;
    loop assigns a, b ;
    loop variant b ;
  */ 
  while (b != 0){
    unsigned t = b;
    b = a % b;
    a = t;
  }
  return a;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid case with a=8 and b=12
void test_case_1() {
    unsigned result = gcd(8, 12);
    printf("test_case_1: %u\n", result);  // Expected: 4
}

// Test case 2: Valid case with a=0 and b=7
void test_case_2() {
    unsigned result = gcd(0, 7);
    printf("test_case_2: %u\n", result);  // Expected: 7
}

// Test case 3: Valid case with a=17 and b=5
void test_case_3() {
    unsigned result = gcd(17, 5);
    printf("test_case_3: %u\n", result);  // Expected: 1
}

// Test case 4: Valid case with a=21 and b=14
void test_case_4() {
    unsigned result = gcd(21, 14);
    printf("test_case_4: %u\n", result);  // Expected: 7
}

// Test case 5: Valid case with a=1 and b=0
void test_case_5() {
    unsigned result = gcd(1, 0);
    printf("test_case_5: %u\n", result);  // Expected: 1
}

// Test case 6: Boundary case with a=0 and b=0
void test_case_6() {
    unsigned result = gcd(0, 0);
    printf("test_case_6: %u\n", result);  // Expected: 0
}

// Test case 7: Boundary case with maximum unsigned value and 1
void test_case_7() {
    unsigned result = gcd(4294967295, 1);
    printf("test_case_7: %u\n", result);  // Expected: 1
}

// Test case 8: Invalid case with a=-5 (violates a >= 0)
void test_case_8() {
    // Explicitly cast to unsigned to simulate invalid input
    unsigned a = (unsigned)-5;
    unsigned result = gcd(a, 10);
    // No output check needed for invalid case
}

// Test case 9: Invalid case with b=-3 (violates b >= 0)
void test_case_9() {
    // Explicitly cast to unsigned to simulate invalid input
    unsigned b = (unsigned)-3;
    unsigned result = gcd(15, b);
    // No output check needed for invalid case
}

// Harness entry point (not main!)
void test_harness_gcd() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called - for precondition testing
}
void test_case_8() {
    unsigned result = gcd(-8, 12);
    assert(result == 4);
}

void test_case_9() {
    unsigned result = gcd(21, -14);
    assert(result == 7);
}