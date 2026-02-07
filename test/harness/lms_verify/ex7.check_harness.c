// ========== Original Code (with ACSL) ==========
#include <limits.h>
/*@ requires ((x1>0) && 
\valid(x0+(0..x1-1)));
assigns \nothing;
ensures (((\result==-1) ==> (!(\exists int  x56; (((0<=x56) && 
(x56<x1)) && 
(x0[x56]==x2))))) && 
((\result!=-1) ==> (((0<=\result) && 
(\result<x1)) && 
(x0[\result]==x2))));
*/
int member(int  * x0, int  x1, int  x2) {
  int x4 = -1;
  /*@ loop invariant ((((0<=x6) && 
(x6<=x1)) && 
((x4==-1) ==> (!(\exists int  x22; (((0<=x22) && 
(x22<x6)) && 
(x0[x22]==x2)))))) && 
((x4!=-1) ==> (((0<=x4) && 
(x4<x6)) && 
(x0[x4]==x2))));
  loop assigns x6, x4;
  loop variant (x1-x6);
  */
  for(int x6=0; x6 < x1; x6++) {
    int x7 = x4;
    int x8 = x7 == -1;
    int x11;
    if (x8) {
      int x9 = x0[x6];
      int x10 = x9 == x2;
      x11 = x10;
    } else {
      x11 = 0/*false*/;
    }
    if (x11) {
      x4 = x6;
    } else {
    }
  }
  int x50 = x4;
  return x50;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - element found in middle
void test_case_1() {
    int arr[] = {1, 2, 3, 4};
    int result = member(arr, 4, 3);
    printf("test_case_1: %d\n", result);  // Expected: 2
}

// Test case 2: Valid - element not found
void test_case_2() {
    int arr[] = {5, 6, 7};
    int result = member(arr, 3, 4);
    printf("test_case_2: %d\n", result);  // Expected: -1
}

// Test case 3: Valid - element at first position
void test_case_3() {
    int arr[] = {10, 20, 30};
    int result = member(arr, 3, 10);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - element at last position
void test_case_4() {
    int arr[] = {10, 20, 30};
    int result = member(arr, 3, 30);
    printf("test_case_4: %d\n", result);  // Expected: 2
}

// Test case 5: Valid - single element match
void test_case_5() {
    int arr[] = {42};
    int result = member(arr, 1, 42);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Invalid - x1 equals zero
void test_case_6() {
    int arr[] = {1, 2, 3};
    int result = member(arr, 0, 1);  // Frama-C should flag this
}

// Test case 7: Invalid - null pointer
void test_case_7() {
    int *arr = NULL;
    int result = member(arr, 3, 1);  // Frama-C should flag this
}

// Test case 8: Boundary - single element no match
void test_case_8() {
    int arr[] = {5};
    int result = member(arr, 1, 6);
    printf("test_case_8: %d\n", result);  // Expected: -1
}

// Test case 9: Boundary - two elements match at last
void test_case_9() {
    int arr[] = {0, 1};
    int result = member(arr, 2, 1);
    printf("test_case_9: %d\n", result);  // Expected: 1
}

// Harness entry point
void test_harness_member() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called
}