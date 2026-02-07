// ========== Original Code (with ACSL) ==========
#include <stddef.h>
#include <limits.h>

/*@
  requires \valid(v_res + (0 .. len-1));
  requires \valid_read(v1 + (0 .. len-1));
  requires \valid_read(v2 + (0 .. len-1));
  requires \separated(v1 + (0 .. len-1), v_res + (0 .. len-1));
  requires \separated(v2 + (0 .. len-1), v_res + (0 .. len-1));

  requires 
    \forall integer i ; 0 <= i < len ==> INT_MIN <= v1[i]+v2[i] <= INT_MAX ;

  assigns v_res[0 .. len-1];
  
  ensures \forall integer i ; 0 <= i < len ==> v_res[i] == v1[i] + v2[i] ;
  ensures \forall integer i ; 0 <= i < len ==> v1[i] == \old(v1[i]) ;
  ensures \forall integer i ; 0 <= i < len ==> v2[i] == \old(v2[i]) ;
*/
void add_vectors(int* v_res, const int* v1, const int* v2, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant 
      \forall integer j ; 0 <= j < i ==> v_res[j] == v1[j] + v2[j] ;
    loop assigns i, v_res[0 .. len-1] ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    v_res[i] = v1[i] + v2[i] ;
  }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - positive integers
void test_case_1() {
    int v1[] = {1, 2, 3};
    int v2[] = {4, 5, 6};
    int v_res[3];
    add_vectors(v_res, v1, v2, 3);
    printf("test_case_1: [%d, %d, %d]\n", v_res[0], v_res[1], v_res[2]);  // Expected: [5, 7, 9]
}

// Test case 2: Valid - negative integers
void test_case_2() {
    int v1[] = {-1, -2};
    int v2[] = {-3, -4};
    int v_res[2];
    add_vectors(v_res, v1, v2, 2);
    printf("test_case_2: [%d, %d]\n", v_res[0], v_res[1]);  // Expected: [-4, -6]
}

// Test case 3: Valid - mixed positive and negative
void test_case_3() {
    int v1[] = {5, -3};
    int v2[] = {-2, 4};
    int v_res[2];
    add_vectors(v_res, v1, v2, 2);
    printf("test_case_3: [%d, %d]\n", v_res[0], v_res[1]);  // Expected: [3, 1]
}

// Test case 4: Valid - all zeros
void test_case_4() {
    int v1[] = {0, 0, 0, 0, 0};
    int v2[] = {0, 0, 0, 0, 0};
    int v_res[5];
    add_vectors(v_res, v1, v2, 5);
    printf("test_case_4: [%d, %d, %d, %d, %d]\n", v_res[0], v_res[1], v_res[2], v_res[3], v_res[4]);  // Expected: [0, 0, 0, 0, 0]
}

// Test case 5: Valid - single element
void test_case_5() {
    int v1[] = {42};
    int v2[] = {13};
    int v_res[1];
    add_vectors(v_res, v1, v2, 1);
    printf("test_case_5: [%d]\n", v_res[0]);  // Expected: [55]
}

// Test case 6: Invalid - NULL v_res pointer
void test_case_6() {
    int v1[] = {1, 2};
    int v2[] = {3, 4};
    add_vectors(NULL, v1, v2, 2);  // Frama-C should flag this
}

// Test case 7: Invalid - overlapping v1 and v_res arrays
void test_case_7() {
    int v1[] = {1, 2};
    int v2[] = {3, 4};
    add_vectors(v1, v1, v2, 2);  // Frama-C should flag this
}

// Test case 8: Boundary - zero length
void test_case_8() {
    int v1[] = {};  // Dummy array
    int v2[] = {};
    int v_res[0];
    add_vectors(v_res, v1, v2, 0);
    printf("test_case_8: (no output expected)\n");  // Expected: No modification
}

// Test case 9: Boundary - sums at INT_MAX and INT_MIN
void test_case_9() {
    int v1[] = {INT_MAX, INT_MIN};
    int v2[] = {0, 0};
    int v_res[2];
    add_vectors(v_res, v1, v2, 2);
    printf("test_case_9: [%d, %d]\n", v_res[0], v_res[1]);  // Expected: [INT_MAX, INT_MIN]
}

// Harness entry point
void test_harness_add_vectors() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6() and test_case_7() intentionally not called - they're for precondition testing
}
void test_case_6() {
    int v1[] = {INT_MAX};
    int v2[] = {1};
    int v_res[1];
    add_vectors(v_res, v1, v2, 1);
}

void test_case_7() {
    int v1[] = {1, 2};
    int v2[] = {3, 4};
    add_vectors(v1, v1, v2, 2); // v_res and v1 overlap
}