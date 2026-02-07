// ========== Original Code (with ACSL) ==========
/*@ logic integer factorial(integer n) = (n <= 0) ? 1 : n * factorial(n-1);
*/

/*@
  requires n <= 12 ;
  assigns \nothing ;
  ensures \result == factorial(n) ;
*/
int facto(int n){
  if(n < 2) return 1 ;

  int res = 1 ;
  /*@
    loop invariant 2 <= i <= n+1 ;
    loop invariant res == factorial(i-1) ;
    loop assigns i, res ;
    loop variant n - i ;
  */
  for(int i = 2 ; i <= n ; i++){
    res = res * i ;
  }
  return res ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - n=1 (base case)
void test_case_1() {
    int result = facto(1);
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - n=2 (small input)
void test_case_2() {
    int result = facto(2);
    printf("test_case_2: %d\n", result);  // Expected: 2
}

// Test case 3: Valid - n=5 (medium input)
void test_case_3() {
    int result = facto(5);
    printf("test_case_3: %d\n", result);  // Expected: 120
}

// Test case 4: Valid - n=11 (close to upper bound)
void test_case_4() {
    int result = facto(11);
    printf("test_case_4: %d\n", result);  // Expected: 39916800
}

// Test case 5: Valid - n=6 (another medium input)
void test_case_5() {
    int result = facto(6);
    printf("test_case_5: %d\n", result);  // Expected: 720
}

// Test case 6: Boundary - n=0 (base case for factorial definition)
void test_case_6() {
    int result = facto(0);
    printf("test_case_6: %d\n", result);  // Expected: 1
}

// Test case 7: Boundary - n=12 (maximum allowed input)
void test_case_7() {
    int result = facto(12);
    printf("test_case_7: %d\n", result);  // Expected: 479001600
}

// Test case 8: Invalid - n=13 (violates n <= 12)
void test_case_8() {
    int result = facto(13);
    // No output check - invalid precondition
}

// Test case 9: Invalid - n=20 (violates n <= 12)
void test_case_9() {
    int result = facto(20);
    // No output check - invalid precondition
}

// Harness entry point (not main!)
void test_harness_facto() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called - for precondition testing
}
void test_case_8() {
    int result = facto(13);
    printf("%d\n", result);
}

void test_case_9() {
    int result = facto(100);
    printf("%d\n", result);
}