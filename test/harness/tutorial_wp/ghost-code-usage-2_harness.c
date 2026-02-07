// ========== Original Code (with ACSL) ==========
/*@ predicate sorted(int* arr, integer end) =
      \forall integer i, j ; 0 <= i <= j < end ==> arr[i] <= arr[j] ;
    predicate element_level_sorted(int* array, integer end) =
      \forall integer i ; 0 <= i < end-1 ==> array[i] <= array[i+1] ;
*/

/*@ requires \valid_read(arr + (0 .. len-1));
    requires sorted(arr, len) ;
*/
size_t bsearch(int* arr, size_t len, int value);

/*@ requires \valid_read(arr + (0 .. len-1));
    requires element_level_sorted(arr, len) ;
*/
unsigned bsearch_callee(int* arr, size_t len, int value){ 
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant sorted(arr, i) ;
    loop assigns i ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    /*@ assert 0 < i ==> arr[i-1] <= arr[i] ; */
  }
  return bsearch(arr, len, value);
}

// ========== Stub Implementation for bsearch ==========
size_t bsearch(int* arr, size_t len, int value) {
    for (size_t i = 0; i < len; i++) {
        if (arr[i] == value) {
            return i;
        }
    }
    return len;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal sorted array
void test_case_1() {
    int arr[] = {1, 2, 3, 4, 5};
    unsigned result = bsearch_callee(arr, 5, 3);
    printf("test_case_1: %u\n", result);  // Expected: 2
}

// Test case 2: Valid - all equal elements
void test_case_2() {
    int arr[] = {5, 5, 5};
    unsigned result = bsearch_callee(arr, 3, 5);
    printf("test_case_2: %u\n", result);  // Expected: 0
}

// Test case 3: Valid - single element
void test_case_3() {
    int arr[] = {10};
    unsigned result = bsearch_callee(arr, 1, 10);
    printf("test_case_3: %u\n", result);  // Expected: 0
}

// Test case 4: Valid - mixed negative and positive values
void test_case_4() {
    int arr[] = {-5, 0, 3, 7};
    unsigned result = bsearch_callee(arr, 4, 0);
    printf("test_case_4: %u\n", result);  // Expected: 1
}

// Test case 5: Valid - empty array with dummy pointer
void test_case_5() {
    int dummy;
    int* arr = &dummy;
    unsigned result = bsearch_callee(arr, 0, 42);
    printf("test_case_5: %u\n", result);  // Expected: 0
}

// Test case 6: Boundary - two equal elements
void test_case_6() {
    int arr[] = {1, 1};
    unsigned result = bsearch_callee(arr, 2, 1);
    printf("test_case_6: %u\n", result);  // Expected: 0
}

// Test case 7: Invalid - array not sorted
void test_case_7() {
    int arr[] = {3, 1, 2};
    unsigned result = bsearch_callee(arr, 3, 2);
    // Frama-C should flag this
}

// Test case 8: Invalid - NULL pointer
void test_case_8() {
    int* arr = NULL;
    unsigned result = bsearch_callee(arr, 2, 5);
    // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_bsearch_callee() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    // test_case_7() and test_case_8() intentionally not called - for precondition testing
}
void test_case_1() {
    int arr[] = {1, 2, 3, 4};
    size_t len = 4;
    int value = 3;
    unsigned expected = 2;
    unsigned result = bsearch_callee(arr, len, value);
    // assert(result == expected);
}
void test_case_2() {
    int arr[] = {10, 20, 30};
    size_t len = 3;
    int value = 15;
    unsigned expected = 3;
    unsigned result = bsearch_callee(arr, len, value);
    // assert(result == expected);
}
void test_case_3() {
    int arr[] = {5};
    size_t len = 1;
    int value = 5;
    unsigned expected = 0;
    unsigned result = bsearch_callee(arr, len, value);
    // assert(result == expected);
}
void test_case_4() {
    int arr[] = {1, 3, 5, 7, 9};
    size_t len = 5;
    int value = 9;
    unsigned expected = 4;
    unsigned result = bsearch_callee(arr, len, value);
    // assert(result == expected);
}
void test_case_5() {
    int arr[] = {2, 4, 6, 8, 10, 12};
    size_t len = 6;
    int value = 1;
    unsigned expected = 6;
    unsigned result = bsearch_callee(arr, len, value);
    // assert(result == expected);
}
void test_case_6() {
    int *arr = NULL;
    size_t len = 0;
    int value = 5;
    unsigned expected = (unsigned)-1;
    unsigned result = bsearch_callee(arr, len, value);
    // assert(result == expected);
}
void test_case_7() {
    int arr[] = {7};
    size_t len = 1;
    int value = 7;
    unsigned expected = 0;
    unsigned result = bsearch_callee(arr, len, value);
    // assert(result == expected);
}
void test_case_8() {
    int arr[] = {3, 1, 2};
    size_t len = 3;
    int value = 2;
    unsigned expected = (unsigned)-1;
    unsigned result = bsearch_callee(arr, len, value);
    // assert(result == expected);
}