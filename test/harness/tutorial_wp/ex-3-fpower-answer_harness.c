// ========== Original Code (with ACSL) ==========
/* run.config
   DEPS: @PTEST_DEPS@ @PTEST_DIR@/@PTEST_NAME@.@PTEST_NUMBER@.session@PTEST_CONFIG@/interactive/*.v
   STDOPT:+"-wp-no-rte -wp-prover alt-ergo,coq -wp-session @PTEST_DIR@/@PTEST_NAME@.@PTEST_NUMBER@.session@PTEST_CONFIG@"
*/

#include <limits.h>

/*@
  inductive is_power(integer x, integer n, integer r) {
  case zero: \forall integer x ; is_power(x, 0, 1) ;
  case N: \forall integer x, n, r ; n > 0 ==> is_power(x, n-1, r) ==> is_power(x, n, r*x) ;
  }
*/

/*@
  axiomatic Power{
    axiom power_even:
        \forall integer x, n, r ;
        n >= 0 ==> is_power(x * x, n, r) ==> is_power(x, n * 2, r) ;

    axiom power_odd:
        \forall integer x, n, rp ;
        n >= 0 ==> is_power(x * x, n, rp) ==> is_power(x, 2 * n + 1, x * rp) ;
    axiom monotonic:
        \forall integer x, n1, n2, r1, r2;
        0 <= n1 <= n2 ==> is_power(x, n1, r1) && is_power(x, n2, r2) ==> r1 <= r2;
  }
*/

/*@
  requires 0 <= n < INT_MAX ;
  requires \exists integer m; is_power(x, n, m) && INT_MIN <= m <= INT_MAX;
  assigns \nothing ;
  ensures is_power(x, n, \result);
*/
int power(int x, int n){
  int r = 1 ;

  /*@
    loop invariant 1 <= i <= n+1 ;
    loop invariant is_power(x, i-1, r) ;
    loop assigns i, r ;
    loop variant n - i ;
  */
  for(int i = 1 ; i <= n ; ++i){
    r *= x ;
  }

  return r ;
}

/*@
  assigns \nothing ;
  ensures is_power(x, n, \result);
*/
unsigned fast_power(unsigned x, unsigned n){
  //@ ghost unsigned n_pre = n;
  unsigned r = 1 ;
  unsigned p = x ;

  /*@
    loop invariant 0 <= n ;
    loop invariant \forall integer v ; is_power(p, n, v) ==> is_power(x, n_pre, r * v) ;
    loop assigns n, r, p ;
    loop variant n ;
  */
  while(n > 0){
    if(n % 2 == 1){
        //@ assert is_power(p, n, r);
        r = r * p ;
    }
    p *= p ;
    n /= 2 ;
  }
  //@ assert is_power(p, n, 1) ;

  return r ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - Positive base and exponent
void test_case_1() {
    int result = power(2, 3);
    printf("test_case_1: %d\n", result);  // Expected: 8
}

// Test case 2: Valid - Zero base with positive exponent
void test_case_2() {
    int result = power(0, 5);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - Negative base and odd exponent
void test_case_3() {
    int result = power(-2, 3);
    printf("test_case_3: %d\n", result);  // Expected: -8
}

// Test case 4: Valid - Base 1 with maximum allowed exponent
void test_case_4() {
    int result = power(1, INT_MAX - 1);
    printf("test_case_4: %d\n", result);  // Expected: 1
}

// Test case 5: Valid - Exponent resulting in maximum valid value below INT_MAX
void test_case_5() {
    int result = power(2, 30);
    printf("test_case_5: %d\n", result);  // Expected: 1073741824
}

// Test case 6: Invalid - Negative exponent violating first precondition
void test_case_6() {
    int result = power(2, -1);
    // No output check - invalid case
}

// Test case 7: Invalid - Exponent leading to overflow (assuming 2^31 exceeds INT_MAX)
void test_case_7() {
    int result = power(2, 31);
    // No output check - invalid case due to overflow
}

// Test case 8: Boundary - Zero exponent
void test_case_8() {
    int result = power(5, 0);
    printf("test_case_8: %d\n", result);  // Expected: 1
}

// Test case 9: Boundary - Maximum allowed exponent with negative base resulting in 1
void test_case_9() {
    int result = power(-1, INT_MAX - 1);
    printf("test_case_9: %d\n", result);  // Expected: 1
}

// Harness entry point (not main!)
void test_harness_power() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // Invalid test cases are not called
}

// ========== Valid Test Cases ==========

// Test case 1: Standard positive power (2^3)
void test_case_1() {
    unsigned result = fast_power(2, 3);
    printf("test_case_1 (2^3): %u\n", result); // Expected: 8
}

// Test case 2: Base raised to power of 0 (x^0 = 1)
void test_case_2() {
    unsigned result = fast_power(5, 0);
    printf("test_case_2 (5^0): %u\n", result); // Expected: 1
}

// Test case 3: Base of 1 (1^n = 1)
void test_case_3() {
    unsigned result = fast_power(1, 100);
    printf("test_case_3 (1^100): %u\n", result); // Expected: 1
}

// Test case 4: Base of 0 (0^n = 0 for n > 0)
void test_case_4() {
    unsigned result = fast_power(0, 5);
    printf("test_case_4 (0^5): %u\n", result); // Expected: 0
}

// Test case 5: Even exponent (Exercise squaring logic)
void test_case_5() {
    unsigned result = fast_power(3, 4);
    printf("test_case_5 (3^4): %u\n", result); // Expected: 81
}

// Test case 6: Large base, small exponent
void test_case_6() {
    unsigned result = fast_power(100, 2);
    printf("test_case_6 (100^2): %u\n", result); // Expected: 10000
}

// Test case 7: Powers of 2 (Boundary of binary representation)
void test_case_7() {
    unsigned result = fast_power(2, 10);
    printf("test_case_7 (2^10): %u\n", result); // Expected: 1024
}

// ========== Invalid Test Cases (Precondition/Safety Testing) ==========

// Test case 8: Invalid - Mathematical Overflow (32-bit unsigned)
// 2^32 is 4,294,967,296, which exceeds UINT_MAX (4,294,967,295).
// Frama-C static analysis would flag this as a potential violation of the 'ensures' 
// if 'is_power' is checked against the actual mathematical result.
void test_case_8() {
    unsigned result = fast_power(2, 32); 
    printf("test_case_8 (2^32 - Overflow expected): %u\n", result);
}

// Test case 9: Invalid - Base overflow on first squaring
// UINT_MAX * UINT_MAX will immediately wrap around due to C's unsigned arithmetic,
// violating the mathematical relationship 'is_power' in the contract.
void test_case_9() {
    unsigned result = fast_power(UINT_MAX, 2);
    printf("test_case_9 (UINT_MAX^2 - Overflow expected): %u\n", result);
}