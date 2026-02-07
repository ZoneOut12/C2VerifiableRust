// ========== Original Code (with ACSL) ==========
#include <stddef.h>

/*@ 
  predicate arr_sorted(int* arr, integer begin, integer end) =
    \forall integer i, j ; begin <= i <= j < end ==> arr[i] <= arr[j] ;

  predicate sorted(int* arr, integer end) =
    arr_sorted(arr, 0, end);

  predicate is_in_array(int value, int* arr, integer begin, integer end) =
    \exists integer j ; begin <= j < end && arr[j] == value ;

  predicate in_array(int value, int* arr, integer end) =
    is_in_array(value, arr, 0, end) ;
*/

/*@ requires \valid_read(arr + (0 .. len-1));
  requires sorted(arr, len) ;

  assigns \nothing ;

  behavior exists:
    assumes in_array(value, arr, len);
    ensures 0 <= \result < len ;
    ensures arr[\result] == value ;

  behavior does_not_exists:
    assumes !in_array(value, arr, len);
    ensures \result == len ;

  complete behaviors ;
  disjoint behaviors ;
*/
size_t bsearch(int* arr, size_t len, int value){
  if(len == 0) return len ;
  
  size_t low = 0 ;
  size_t up = len ;

  /*@
    loop invariant 0 <= low && up <= len ;
    loop invariant 
      \forall integer i ; 0 <= i < len && arr[i] == value ==> low <= i < up ;
    loop assigns low, up ;
    loop variant up - low ;
  */
  while(low < up){
    size_t mid = low + (up - low)/2 ;
    if     (arr[mid] > value) up = mid ;
    else if(arr[mid] < value) low = mid+1 ;
    else return mid ;
  }
  return len ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - value present in middle
void test_case_1() {
    int arr[] = {1,2,3,4,5};
    size_t result = bsearch(arr, 5, 3);
    printf("test_case_1: %zu\n", result);  // Expected: 2
}

// Test case 2: Valid - value not present
void test_case_2() {
    int arr[] = {1,2,3,4,5};
    size_t result = bsearch(arr, 5, 6);
    printf("test_case_2: %zu\n", result);  // Expected: 5
}

// Test case 3: Valid - single element present
void test_case_3() {
    int arr[] = {42};
    size_t result = bsearch(arr, 1, 42);
    printf("test_case_3: %zu\n", result);  // Expected: 0
}

// Test case 4: Valid - single element not present
void test_case_4() {
    int arr[] = {42};
    size_t result = bsearch(arr, 1, 5);
    printf("test_case_4: %zu\n", result);  // Expected: 1
}

// Test case 5: Valid - value at end
void test_case_5() {
    int arr[] = {10,20,30};
    size_t result = bsearch(arr, 3, 30);
    printf("test_case_5: %zu\n", result);  // Expected: 2
}

// Test case 6: Invalid - null array pointer
void test_case_6() {
    size_t result = bsearch(NULL, 3, 5);  // Frama-C should flag this
}

// Test case 7: Invalid - unsorted array
void test_case_7() {
    int arr[] = {3,1,2};
    size_t result = bsearch(arr, 3, 2);  // Frama-C should flag unsorted
}

// Test case 8: Boundary - empty array
void test_case_8() {
    int arr[] = {0};  // Dummy, won't be accessed
    size_t result = bsearch(arr, 0, 42);
    printf("test_case_8: %zu\n", result);  // Expected: 0
}

// Test case 9: Boundary - value found at mid-point
void test_case_9() {
    int arr[] = {1,3,5};
    size_t result = bsearch(arr, 3, 3);
    printf("test_case_9: %zu\n", result);  // Expected: 1
}

// Harness entry point (not main!)
void test_harness_bsearch() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called - for precondition testing
}
void test_case_6() {
    size_t result = bsearch(NULL, 3, 5);
    assert(result == (size_t)-1);
}

void test_case_7() {
    int arr[] = {1, 3, 2};
    size_t len = 3;
    size_t result = bsearch(arr, len, 2);
    assert(result == 2);
}