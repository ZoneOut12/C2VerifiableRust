// ========== Original Code (with ACSL) ==========
#include <limits.h>

/*@ logic integer sum_of_n_integers(integer n) = (n <= 0) ? 0 : sum_of_n_integers(n-1) + n ; @*/

/*@ ghost
  /@ assigns \nothing ; ensures (n*(n+1)) / 2 == sum_of_n_integers(n) ; @/
  void lemma_value_of_sum_of_n_integers_2(unsigned n){
    /@ loop invariant 0 <= i <= n ; loop invariant (i*(i+1)) == 2 * sum_of_n_integers(i) ; loop assigns i ; loop variant n - i ; @/
    for(unsigned i = 0 ; i < n ; ++i);
  }
*/

/*@ logic integer sum_of_range_of_integers(integer fst, integer lst) = ((lst <= fst) ? lst : lst + sum_of_range_of_integers(fst, lst-1)) ; @*/

/*@ ghost
  /@ requires fst <= lst ; assigns \nothing ; ensures ((lst-fst+1)*(fst+lst))/2 == sum_of_range_of_integers(fst, lst) ; @/
  void lemma_value_of_sum_of_range_of_integers(int fst, int lst){
    /@ loop invariant fst <= i <= lst ; loop invariant (i-fst+1)*(fst+i) == 2 * sum_of_range_of_integers(fst, i) ; loop assigns i ; loop variant lst - i ; @/
    for(int i = fst ; i < lst ; ++i);
  }
*/

/*@ requires n*(n+1) <= UINT_MAX ; assigns \nothing ; ensures \result == sum_of_n_integers(n); @*/
unsigned sum_n(unsigned n){
  //@ ghost lemma_value_of_sum_of_n_integers_2(n);
  //@ assert n * (n+1) >= 0 ; // necessary in Scandium
  return (n*(n+1))/2 ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - n=1
void test_case_1() {
    unsigned result = sum_n(1);
    printf("test_case_1: %u\n", result);  // Expected: 1
}

// Test case 2: Valid - n=5
void test_case_2() {
    unsigned result = sum_n(5);
    printf("test_case_2: %u\n", result);  // Expected: 15
}

// Test case 3: Valid - n=100
void test_case_3() {
    unsigned result = sum_n(100);
    printf("test_case_3: %u\n", result);  // Expected: 5050
}

// Test case 4: Valid - n=10
void test_case_4() {
    unsigned result = sum_n(10);
    printf("test_case_4: %u\n", result);  // Expected: 55
}

// Test case 5: Valid - n=65534
void test_case_5() {
    unsigned result = sum_n(65534);
    printf("test_case_5: %u\n", result);  // Expected: 2147385345
}

// Test case 6: Boundary - n=0
void test_case_6() {
    unsigned result = sum_n(0);
    printf("test_case_6: %u\n", result);  // Expected: 0
}

// Test case 7: Boundary - n=65535
void test_case_7() {
    unsigned result = sum_n(65535);
    printf("test_case_7: %u\n", result);  // Expected: 2147483640
}

// Test case 8: Invalid - n=65536
void test_case_8() {
    unsigned result = sum_n(65536);
    // No output check
}

// Test case 9: Invalid - n=100000
void test_case_9() {
    unsigned result = sum_n(100000);
    // No output check
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
    // test_case_8 and test_case_9 intentionally not called
}
void test_case_8() {
  ASSERT(sum_n(65536) == 2147483648);
}
void test_case_9() {
  ASSERT(sum_n(65537) == 2147549185);
}