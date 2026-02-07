// ========== Original Code (with ACSL) ==========
#include <stddef.h>

/*@
  requires \valid_read(arr + (0 .. len-1));
  requires Sorted:
    \forall integer i, j ; 0 <= i <= j < len ==> arr[i] <= arr[j] ;

  assigns \nothing ;

  behavior exists:
    assumes \exists integer j ; 0 <= j < len && arr[j] == value ;
    ensures 0 <= \result < len ;
    ensures arr[\result] == value ;

  behavior does_not_exists:
    assumes \forall integer j ; 0 <= j < len ==> arr[j] != value ;
    ensures \result == len ;

  complete behaviors ;
  disjoint behaviors ;
*/
size_t bsearch(int* arr, size_t len, int value){
  if(len == 0) return 0 ;
  
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

// Test case 1: Valid - value in middle
void test_case_1() {
    int arr[] = {1, 2, 3, 4, 5};
    size_t result = bsearch(arr, 5, 3);
    printf("test_case_1: %zu\n", result);  // Expected: 2
}

// Test case 2: Valid - value at start
void test_case_2() {
    int arr[] = {10, 20, 30};
    size_t result = bsearch(arr, 3, 10);
    printf("test_case_2: %zu\n", result);  // Expected: 0
}

// Test case 3: Valid - value at end
void test_case_3() {
    int arr[] = {5, 6, 7};
    size_t result = bsearch(arr, 3, 7);
    printf("test_case_3: %zu\n", result);  // Expected: 2
}

// Test case 4: Valid - value not present
void test_case_4() {
    int arr[] = {2, 4, 6, 8};
    size_t result = bsearch(arr, 4, 5);
    printf("test_case_4: %zu\n", result);  // Expected: 4
}

// Test case 5: Valid - single element match
void test_case_5() {
    int arr[] = {5};
    size_t result = bsearch(arr, 1, 5);
    printf("test_case_5: %zu\n", result);  // Expected: 0
}

// Test case 6: Invalid - null array
void test_case_6() {
    bsearch(NULL, 3, 0);  // Frama-C should flag invalid precondition
}

// Test case 7: Invalid - unsorted array
void test_case_7() {
    int arr[] = {3, 1, 2};
    bsearch(arr, 3, 2);  // Frama-C should flag sorted precondition violation
}

// Test case 8: Boundary - empty array
void test_case_8() {
    size_t result = bsearch(NULL, 0, 42);
    printf("test_case_8: %zu\n", result);  // Expected: 0
}

// Test case 9: Boundary - single element no match
void test_case_9() {
    int arr[] = {5};
    size_t result = bsearch(arr, 1, 3);
    printf("test_case_9: %zu\n", result);  // Expected: 1
}

// Harness entry point
void test_harness_bsearch() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // Invalid cases intentionally not called for precondition testing
}
void test_case_6() {
    int* arr = NULL;
    size_t len = 3;
    int value = 5;
    size_t result = bsearch(arr, len, value);
}
void test_case_7() {
    int arr[] = {3, 1, 2};
    size_t len = 3;
    int value = 2;
    size_t result = bsearch(arr, len, value);
}