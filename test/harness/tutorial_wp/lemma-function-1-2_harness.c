// ========== Original Code (with ACSL) ==========
#include <stddef.h>
#include <limits.h>

/*@ predicate sorted(int* arr, integer end) =
      \forall integer i, j ; 0 <= i <= j < end ==> arr[i] <= arr[j] ;
    predicate element_level_sorted(int* array, integer end) =
      \forall integer i ; 0 <= i < end-1 ==> array[i] <= array[i+1] ; 
*/

/*@ requires \valid_read(arr + (0 .. len-1));
    requires sorted(arr, len) ;
*/
size_t bsearch(int* arr, size_t len, int value);

/*@ requires element_level_sorted(arr, len) ;
  assigns  \nothing ;
  ensures  sorted(arr, len);
*/
void element_level_sorted_implies_sorted(int* arr, size_t len){
  /*@ loop invariant 0 <= i <= len ;
    loop invariant sorted(arr, i) ;
    loop assigns i ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    //@ assert 0 < i ==> arr[i-1] <= arr[i] ;
  }
}

/*@ requires \valid_read(arr + (0 .. len-1));
    requires element_level_sorted(arr, len) ;
*/
unsigned bsearch_callee(int* arr, size_t len, int value){
  element_level_sorted_implies_sorted(arr, len) ;
  return bsearch(arr, len, value);
}

// Dummy implementation for bsearch
size_t bsearch(int* arr, size_t len, int value) {
    return 0;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - sorted array with 4 elements
void test_case_valid_1() {
    int arr[] = {1, 2, 3, 4};
    unsigned result = bsearch_callee(arr, 4, 3);
    printf("test_case_valid_1: %u\n", result);
}

// Test case 2: Valid - all equal elements
void test_case_valid_2() {
    int arr[] = {2, 2, 2};
    unsigned result = bsearch_callee(arr, 3, 2);
    printf("test_case_valid_2: %u\n", result);
}

// Test case 3: Valid - array with duplicates
void test_case_valid_3() {
    int arr[] = {0, 0, 1, 2};
    unsigned result = bsearch_callee(arr, 4, 1);
    printf("test_case_valid_3: %u\n", result);
}

// Test case 4: Valid - single-element array
void test_case_valid_4() {
    int arr[] = {5};
    unsigned result = bsearch_callee(arr, 1, 5);
    printf("test_case_valid_4: %u\n", result);
}

// Test case 5: Valid - non-strictly increasing array
void test_case_valid_5() {
    int arr[] = {1, 3, 3, 5};
    unsigned result = bsearch_callee(arr, 4, 3);
    printf("test_case_valid_5: %u\n", result);
}

// Test case 6: Boundary - empty array
void test_case_boundary_6() {
    int* arr = NULL;
    unsigned result = bsearch_callee(arr, 0, 10);
    printf("test_case_boundary_6: %u\n", result);
}

// Test case 7: Boundary - single-element array
void test_case_boundary_7() {
    int arr[] = {42};
    unsigned result = bsearch_callee(arr, 1, 42);
    printf("test_case_boundary_7: %u\n", result);
}

// Test case 8: Invalid - NULL pointer with len > 0
void test_case_invalid_8() {
    int* arr = NULL;
    unsigned result = bsearch_callee(arr, 2, 5);
}

// Test case 9: Invalid - unsorted array
void test_case_invalid_9() {
    int arr[] = {3, 1};
    unsigned result = bsearch_callee(arr, 2, 2);
}

// Harness entry point
void test_harness_bsearch_callee() {
    test_case_valid_1();
    test_case_valid_2();
    test_case_valid_3();
    test_case_valid_4();
    test_case_valid_5();
    test_case_boundary_6();
    test_case_boundary_7();
    // Invalid test cases not called to avoid runtime errors
}
void test_case_1() {
    int arr[] = {1,3,5,7};
    size_t len = 4;
    int value = 5;
    unsigned result = bsearch_callee(arr, len, value);
    // Expected: 2
}

void test_case_2() {
    int arr[] = {2,4,6,8};
    size_t len = 4;
    int value = 5;
    unsigned result = bsearch_callee(arr, len, value);
    // Expected: 4
}

void test_case_3() {
    int arr[] = {1,2,2,3};
    size_t len = 4;
    int value = 2;
    unsigned result = bsearch_callee(arr, len, value);
    // Expected: 1
}

void test_case_4() {
    int arr[] = {10,20,30};
    size_t len = 3;
    int value = 10;
    unsigned result = bsearch_callee(arr, len, value);
    // Expected: 0
}

void test_case_5() {
    int arr[] = {10,20,30};
    size_t len = 3;
    int value = 30;
    unsigned result = bsearch_callee(arr, len, value);
    // Expected: 2
}

void test_case_6() {
    int arr[] = {5};
    size_t len = 1;
    int value = 5;
    unsigned result = bsearch_callee(arr, len, value);
    // Expected: 0
}

void test_case_7() {
    int arr[] = {5,10};
    size_t len = 2;
    int value = 10;
    unsigned result = bsearch_callee(arr, len, value);
    // Expected: 1
}

void test_case_8() {
    int* arr = NULL;
    size_t len = 3;
    int value = 0;
    unsigned result = bsearch_callee(arr, len, value);
    // Expected to fail valid_read precondition
}

void test_case_9() {
    int arr[] = {3,1,2};
    size_t len = 3;
    int value = 2;
    unsigned result = bsearch_callee(arr, len, value);
    // Expected to fail sorted precondition
}