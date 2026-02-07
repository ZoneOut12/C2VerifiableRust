#include <stdio.h>
#include <limits.h>

/*@
  axiomatic Factorial {
  logic integer fact(integer n);
  
  axiom case_n:
    \forall integer n;
    n >= 1 ==> fact(n) == n*fact(n-1);
  axiom case_0:
    fact(0) == 1;
  axiom monotonic:
    \forall integer n;
    n >= 0 ==> fact(n+1) > fact(n);
  }
*/

/*@
  requires  0 <= n < INT_MAX;
  ensures   \result == fact(n);
  assigns   \nothing ; 
*/
int factorial(int n) {
  int i = 1;
  int f = 1;
  /*@
    loop invariant f == fact(i-1);
    loop invariant 0 < i;
    loop invariant i <= n+1;
    loop assigns i, f;
    loop variant n + 1 - i;
  */
  while (i <= n)  {
    f = f * i;
    i = i + 1;
  }
  return f;
}

// ========== Test Cases ==========
// Test case 1: Standard positive integer
void test_case_1() {
    int n = 5;
    int result = factorial(n);
    printf("test_case_1 (n=5): %d (Expected: 120)\n", result);
    assert(result == 120);
}

// Test case 2: Zero (Base case)
void test_case_2() {
    int n = 0;
    int result = factorial(n);
    printf("test_case_2 (n=0): %d (Expected: 1)\n", result);
    assert(result == 1);
}

// Test case 3: One (Identity case)
void test_case_3() {
    int n = 1;
    int result = factorial(n);
    printf("test_case_3 (n=1): %d (Expected: 1)\n", result);
    assert(result == 1);
}

// Test case 4: Maximum n before 32-bit signed overflow
// 12! = 479,001,600 (Fits in int)
// 13! = 6,227,020,800 (Overflows int)
void test_case_4() {
    int n = 12;
    int result = factorial(n);
    printf("test_case_4 (n=12): %d (Expected: 479001600)\n", result);
    assert(result == 479001600);
}

// Test case 5: Invalid - Negative input
void test_case_5() {
    int n = -1;
    // Frama-C/ACSL would flag this as a "requires 0 <= n" violation.
    printf("test_case_5 (n=-1): Potential Precondition Violation\n");
}

// Test case 6: Invalid - Large n causing C overflow
// Even if ACSL ensures fact(n), C's int cannot store fact(15)
void test_case_6() {
    int n = 15;
    int result = factorial(n);
    printf("test_case_6 (n=15): %d (Result is garbage due to C overflow)\n", result);
}

// Test case 7: Valid - Small prime number
void test_case_7() {
    int n = 2;
    int result = factorial(n);
    printf("test_case_7 (n=2): %d (Expected: 2)\n", result);
    assert(result == 2);
}

// Test case 8: Valid - Regular positive integer
void test_case_8() {
    int n = 3;
    int result = factorial(n);
    printf("test_case_8 (n=3): %d (Expected: 6)\n", result);
    assert(result == 6);
}

// Test case 9: Valid - Large value within range
void test_case_9() {
    int n = 10;
    int result = factorial(n);
    printf("test_case_9 (n=10): %d (Expected: 3628800)\n", result);
    assert(result == 3628800);
}

// Test Harness Entry Point
void test_harness_factorial() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_7();
    test_case_8();
    test_case_9();
    // test_case_5 and 6 are for boundary/negative testing
}