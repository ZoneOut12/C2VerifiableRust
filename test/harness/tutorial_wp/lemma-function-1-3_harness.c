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

/*@ 
  requires \forall integer i ; 0 <= i < len-1 ==> arr[i] <= arr[i+1] ;
  assigns  \nothing ;
  ensures  \forall integer i, j ; 0 <= i <= j < len ==> arr[i] <= arr[j] ;
*/
void element_level_sorted_implies_sorted(int* arr, size_t len){
  /*@ 
    loop invariant 0 <= i <= len ;
    loop invariant sorted(arr, i) ;
    loop assigns i ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    //@ assert 0 < i ==> arr[i-1] <= arr[i] ; 
  }
}

/*@ 
  requires \forall integer i ; 0 <= i < len-1 ==> arr[i] <= arr[i+1] ;
  assigns  \nothing ;
  ensures  0 <= i <= j < len ==> arr[i] <= arr[j] ;
*/
void element_level_sorted_implies_greater(int* arr, size_t len, size_t i, size_t j){
  element_level_sorted_implies_sorted(arr, len);
}

/*@ 
  requires \forall integer i ; 0 <= i < len-1 ==> arr[i] <= arr[i+1] ;
  requires 0 <= i <= j < len ;
  assigns  \nothing ;
  ensures  arr[i] <= arr[j] ;
*/
void element_level_sorted_implies_greater_2(int* arr, size_t len, size_t i, size_t j){
  element_level_sorted_implies_sorted(arr, len);
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid sorted array with i < j
void test_case_1() {
    int arr[] = {1, 2, 3, 4, 5};
    element_level_sorted_implies_greater_2(arr, 5, 1, 3);
}

// Test case 2: Valid array with all equal elements
void test_case_2() {
    int arr[] = {2, 2, 2};
    element_level_sorted_implies_greater_2(arr, 3, 0, 2);
}

// Test case 3: Valid sorted array with increasing values
void test_case_3() {
    int arr[] = {1, 3, 5, 7};
    element_level_sorted_implies_greater_2(arr, 4, 0, 3);
}

// Test case 4: Boundary single element array
void test_case_4() {
    int arr[] = {5};
    element_level_sorted_implies_greater_2(arr, 1, 0, 0);
}

// Test case 5: Boundary two elements
void test_case_5() {
    int arr[] = {1, 2};
    element_level_sorted_implies_greater_2(arr, 2, 0, 1);
}

// Test case 6: Invalid array not element-level sorted
void test_case_6() {
    int arr[] = {3, 1, 2};
    element_level_sorted_implies_greater_2(arr, 3, 0, 2);
}

// Test case 7: Invalid i > j
void test_case_7() {
    int arr[] = {1, 2, 3};
    element_level_sorted_implies_greater_2(arr, 3, 2, 1);
}

// Harness entry point
void test_harness_element_level_sorted_implies_greater_2() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // test_case_6() and test_case_7() intentionally not called for precondition testing
}
void test_case_6() {
    int arr[] = {1, 2, 5, 3};
    element_level_sorted_implies_greater_2(arr, 4, 0, 3);
}

void test_case_7() {
    int arr[] = {10, 20, 30};
    element_level_sorted_implies_greater_2(arr, 3, 2, 1);
}