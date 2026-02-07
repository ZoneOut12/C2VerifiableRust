// ========== Original Code (with ACSL) ==========
#include <stddef.h>

/*@ requires \valid_read(arr + (0 .. len-1));
  requires Sorted:
    \forall integer i, j ; 0 <= i <= j < len ==> arr[i] <= arr[j] ;
  requires len >= 0 ;
    
  assigns \nothing ;

  ensures -1 <= \result < len ;

  behavior exists:
    assumes \exists integer j ; 0 <= j < len && arr[j] == value ;
    ensures arr[\result] == value ;

  behavior does_not_exists:
    assumes \forall integer j ; 0 <= j < len ==> arr[j] != value ;
    ensures \result == -1 ;

  complete behaviors ;
  disjoint behaviors ;
*/
int bsearch(int* arr, int len, int value){
  if(len == 0) return -1 ;
  
  int low = 0 ;
  int up = len-1 ;

  /*@
    loop invariant 0 <= low && up < len ;
    loop invariant 
      \forall integer i ; 0 <= i < len && arr[i] == value ==> low <= i <= up ;
    loop assigns low, up ;
    loop variant up - low ;
  */
  while(low <= up){
    int mid = low + (up - low)/2 ;
    if     (arr[mid] > value) up = mid-1 ;
    else if(arr[mid] < value) low = mid+1 ;
    else return mid ;
  }
  return -1 ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - value in middle
void test_case_1() {
    int arr[] = {1,2,3,4,5};
    int result = bsearch(arr, 5, 3);
    printf("test_case_1: %d\n", result);  // Expected: 2
}

// Test case 2: Valid - first element
void test_case_2() {
    int arr[] = {10,20,30};
    int result = bsearch(arr, 3, 10);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - last element
void test_case_3() {
    int arr[] = {5,6,7,8};
    int result = bsearch(arr, 4, 8);
    printf("test_case_3: %d\n", result);  // Expected: 3
}

// Test case 4: Valid - single element found
void test_case_4() {
    int arr[] = {42};
    int result = bsearch(arr, 1, 42);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid - single element not found
void test_case_5() {
    int arr[] = {42};
    int result = bsearch(arr, 1, 0);
    printf("test_case_5: %d\n", result);  // Expected: -1
}

// Test case 6: Boundary - empty array
void test_case_6() {
    int arr[] = {0};  // Dummy, won't be accessed
    int result = bsearch(arr, 0, 5);
    printf("test_case_6: %d\n", result);  // Expected: -1
}

// Test case 7: Boundary - all elements same
void test_case_7() {
    int arr[] = {2,2,2,2};
    int result = bsearch(arr, 4, 2);
    printf("test_case_7: %d\n", result);  // Expected: 1
}

// Test case 8: Invalid - negative length
void test_case_8() {
    int arr[] = {1,2,3};
    int result = bsearch(arr, -1, 0);  // Frama-C should flag this
}

// Test case 9: Invalid - unsorted array
void test_case_9() {
    int arr[] = {1,3,2,4};
    int result = bsearch(arr, 4, 2);
}

// Harness entry point (not main!)
void test_harness_bsearch() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called
}