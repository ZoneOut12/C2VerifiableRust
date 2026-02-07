// ========== Original Code (with ACSL) ==========
#include <stddef.h>
#include <limits.h>

/*@ predicate sorted(int* arr, integer end) =
      \\forall integer i, j ; 0 <= i <= j < end ==> arr[i] <= arr[j] ;
    predicate element_level_sorted(int* array, integer end) =
      \\forall integer i ; 0 <= i < end-1 ==> array[i] <= array[i+1] ; 
*/

/*@ requires \\valid_read(arr + (0 .. len-1));
    requires sorted(arr, len) ;
*/
size_t bsearch(int* arr, size_t len, int value);

/*@ requires \\valid_read(arr + (0 .. len-1));
    requires element_level_sorted(arr, len) ;
*/
unsigned bsearch_callee(int* arr, size_t len, int value){
  // ghost element_level_sorted_implies_sorted(arr, len) ;
  /*@ assert element_level_sorted(arr, len) ; */
  /*@ loop invariant 0 <= i <= len ;                   
     loop invariant sorted(arr, i) ;                  
     loop assigns i ;                                  
     loop variant len-i ; 
  */
     for(size_t i = 0 ; i < len ; ++i){           
    /*@ assert 0 < i ==> arr[i-1] <= arr[i] ; */
  }                                                     
  /*@ assert sorted(arr, len); */
  return bsearch(arr, len, value);
}

// Dummy implementation for linking
size_t bsearch(int* arr, size_t len, int value) {
    return 0;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal sorted array
void test_case_1() {
    int arr[] = {1, 2, 3, 4, 5};
    unsigned result = bsearch_callee(arr, 5, 3);
    printf("test_case_1: %u\n", result);  // Expected: 0 (stub)
}

// Test case 2: Valid - value not present
void test_case_2() {
    int arr[] = {1, 2, 3, 4, 5};
    unsigned result = bsearch_callee(arr, 5, 6);
    printf("test_case_2: %u\n", result);  // Expected: 0 (stub)
}

// Test case 3: Valid - duplicates
void test_case_3() {
    int arr[] = {2, 2, 2};
    unsigned result = bsearch_callee(arr, 3, 2);
    printf("test_case_3: %u\n", result);  // Expected: 0 (stub)
}

// Test case 4: Valid - single element
void test_case_4() {
    int arr[] = {42};
    unsigned result = bsearch_callee(arr, 1, 42);
    printf("test_case_4: %u\n", result);  // Expected: 0 (stub)
}

// Test case 5: Valid - empty array
void test_case_5() {
    int* arr = NULL;
    unsigned result = bsearch_callee(arr, 0, 5);
    printf("test_case_5: %u\n", result);  // Expected: 0 (stub)
}

// Test case 6: Invalid - array not sorted
void test_case_6() {
    int arr[] = {3, 1, 2};
    unsigned result = bsearch_callee(arr, 3, 1);
    // No output check for invalid case
}

// Test case 7: Invalid - NULL array with len>0
void test_case_7() {
    int* arr = NULL;
    unsigned result = bsearch_callee(arr, 2, 5);
    // No output check for invalid case
}

// Test case 8: Boundary - empty array
void test_case_8() {
    int* arr = NULL;
    unsigned result = bsearch_callee(arr, 0, 10);
    printf("test_case_8: %u\n", result);  // Expected: 0 (stub)
}

// Test case 9: Boundary - single element
void test_case_9() {
    int arr[] = {5};
    unsigned result = bsearch_callee(arr, 1, 5);
    printf("test_case_9: %u\n", result);  // Expected: 0 (stub)
}

// Harness entry point
void test_harness_bsearch_callee() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called
}
void test_case_6() {
    int *arr = NULL;
    size_t len = 3;
    int value = 5;
    unsigned result = bsearch_callee(arr, len, value);
}

void test_case_7() {
    int arr[] = {2, 1, 3};
    size_t len = 3;
    int value = 1;
    unsigned result = bsearch_callee(arr, len, value);
}