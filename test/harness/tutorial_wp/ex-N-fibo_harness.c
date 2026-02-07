// ========== Original Code (with ACSL) ==========
#include <limits.h>

/*@
  inductive is_fibo(integer n, integer r){
  case fib_0: is_fibo(0, 1) ;
  case fib_1: is_fibo(1, 1) ;
  case fib_N: 
    \forall integer n, p_1, p_2 ;
    n > 1 ==> is_fibo(n-2, p_2) ==> is_fibo(n-1, p_1) ==> is_fibo(n, p_2+p_1) ;
  }
*/

/*@ admit lemma fib_monotonic:
      \forall integer i, j, n1, n2;
        i <= j && is_fibo(i, n1) && is_fibo(j, n2) ==> n1 <= n2;
*/

/*@
  requires n > 1 && is_fibo(n-2, p_2) && is_fibo(n-1, p_1) ;
  assigns \nothing ;
  ensures is_fibo(n, p_2+p_1) ;
*/
void helper(int n, int p_1, int p_2){}

/*@
  requires n >= 0 ;
  requires \exists integer m; is_fibo(n, m) && 0 < m <= INT_MAX;
  assigns  \nothing ;
  ensures  is_fibo(n, \result);
*/
int fibo(int n){
  if(n < 2) return 1 ;

  int p_1 = 1 ;
  int r = p_1 + 1 ;

  //@ ghost helper(2, p_1, 1);
  //@ assert is_fibo(2, r); 
  /*@
    loop invariant 2 <= i <= n ;
    loop invariant is_fibo(i-1, p_1) ;
    loop invariant is_fibo(i, r) ;
    loop assigns i, p_1, r ;
    loop variant n - i ;
  */
  for(int i = 2 ; i < n ; ++i){
    int x = r + p_1 ;
    //@ ghost helper(i+1, r, p_1);
    p_1 = r ;
    r = x ;
  }
  return r ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - base case n=0
void test_case_1() {
    int result = fibo(0);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - base case n=1
void test_case_2() {
    int result = fibo(1);
    printf("test_case_2: %d\n", result);  // Expected: 1
}

// Test case 3: Valid - Fibonacci(5) = 8
void test_case_3() {
    int result = fibo(5);
    printf("test_case_3: %d\n", result);  // Expected: 8
}

// Test case 4: Valid - Fibonacci(10) = 89
void test_case_4() {
    int result = fibo(10);
    printf("test_case_4: %d\n", result);  // Expected: 89
}

// Test case 5: Valid - Maximum allowed Fibonacci before INT_MAX
void test_case_5() {
    int result = fibo(45);
    printf("test_case_5: %d\n", result);  // Expected: 1836311903
}

// Test case 6: Invalid - n < 0
void test_case_6() {
    int result = fibo(-1);  // Frama-C should flag this
}

// Test case 7: Invalid - Fibonacci(46) exceeds INT_MAX
void test_case_7() {
    int result = fibo(46);  // Frama-C should flag this
}

// Test case 8: Boundary - Minimum allowed value n=0
void test_case_8() {
    int result = fibo(0);
    printf("test_case_8: %d\n", result);  // Expected: 1
}

// Test case 9: Boundary - Maximum allowed Fibonacci value
void test_case_9() {
    int result = fibo(45);
    printf("test_case_9: %d\n", result);  // Expected: 1836311903
}

// Harness entry point (not main!)
void test_harness_fibo() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // Invalid test cases intentionally not called - they're for precondition testing
}