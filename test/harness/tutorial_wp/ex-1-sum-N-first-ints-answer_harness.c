// ========== Original Code (with ACSL) ==========
/*@ requires n >= 0;
    requires \valid(arr + (0..n-1));
    assigns \nothing;
*/

/*@ inductive is_sum_n(integer n, integer res) {
  case nul:     \forall integer n ; n <= 0 ==> is_sum_n(n, 0) ;
  case not_nul: \forall integer n, p ; n > 0 ==> is_sum_n(n-1, p) ==> is_sum_n(n, n+p) ;
  }
*/

/*@ admit lemma sum_n_value_direct:
    \forall integer n, r ;
      n >= 0 ==> is_sum_n(n, r) ==> r == (n*(n+1))/2 ;
*/

/*@ requires n*(n+1) <= 2*INT_MAX ;
  assigns \nothing ;
  ensures is_sum_n(n, \result) ;
*/
int sum_n(int n){
  if(n < 1) return 0 ;

  int res = 0 ;
  /*@ loop invariant 1 <= i <= n+1 ;
      loop invariant is_sum_n(i-1, res) ;
      loop assigns i, res ;
      loop variant n - i ;
  */
  for(int i = 1 ; i <= n ; i++){
    res += i ;
  }
  return res ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - n=1
void test_case_1() {
    int result = sum_n(1);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - n=5
void test_case_2() {
    int result = sum_n(5);
    printf("test_case_2: %d\n", result);  // Expected: 15
}

// Test case 3: Valid - n=100
void test_case_3() {
    int result = sum_n(100);
    printf("test_case_3: %d\n", result);  // Expected: 5050
}

// Test case 4: Valid - n=1000
void test_case_4() {
    int result = sum_n(1000);
    printf("test_case_4: %d\n", result);  // Expected: 500500
}

// Test case 5: Valid - n=12345
void test_case_5() {
    int result = sum_n(12345);
    printf("test_case_5: %d\n", result);  // Expected: 76205685
}

// Test case 6: Boundary - n=0
void test_case_6() {
    int result = sum_n(0);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary - n=65535
void test_case_7() {
    int result = sum_n(65535);
    printf("test_case_7: %d\n", result);  // Expected: 2147450880
}

// Test case 8: Invalid - n=65536
void test_case_8() {
    int result = sum_n(65536);  // Frama-C should flag this
}

// Test case 9: Invalid - n=-65537
void test_case_9() {
    int result = sum_n(-65537);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_sum_n() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called - for precondition testing
}