// ========== Original Code (with ACSL) ==========
/*@ requires n >= 0;
    requires \valid(base + (0 .. n-1));
    requires \forall integer k1, integer k2; 0 <= k1 < k2 < n ==> base[k1] <= base[k2];
    
    assigns \nothing;
    ensures \result >= -1 && \result < n;

    behavior present:
        assumes \exists integer k ; 0 <= k < n && base[k] == key ;
        ensures base[\result] == key ;

    behavior not_present:
        assumes \forall integer k ; 0 <= k < n ==> base[k] != key ;
        ensures \result == -1;

    disjoint behaviors;
    complete behaviors;
 */
int binsearch(int *base, int n, int key)
{
   int l = 0;
   int h = n - 1;

   /*@ loop invariant 0 <= l;
       loop invariant h < n;
       loop invariant \forall integer i; 0 <= i < n && base[i] == key ==> l <= i <= h;
       loop assigns l, h;
       loop variant h - l;
    */
   while (l <= h) {
      // INCORRECT: int m = (h + l) / 2;
      int m = l + (h - l) / 2;
      int val = base[m];

      if (val < key) {
         l = m + 1;
         //@ assert \forall integer k1, integer k2; 0 <= k1 < k2 < l ==> base[k1] <= base[k2];
         //@ assert base[m] < key && m == l - 1;
      } else if (val > key) {
         h = m - 1;
      } else {
         //@ assert \forall integer i; 0 <= i < n && base[i] == key ==> l <= i <= h;
         return m;
      }
   }

   return -1;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - key in middle
void test_case_1() {
    int arr[] = {1, 2, 3, 4, 5};
    int result = binsearch(arr, 5, 3);
    printf("test_case_1: %d\n", result);  // Expected: 2
}

// Test case 2: Valid - key not present
void test_case_2() {
    int arr[] = {1, 2, 3, 4, 5};
    int result = binsearch(arr, 5, 6);
    printf("test_case_2: %d\n", result);  // Expected: -1
}

// Test case 3: Valid - single element present
void test_case_3() {
    int arr[] = {42};
    int result = binsearch(arr, 1, 42);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - single element not present
void test_case_4() {
    int arr[] = {42};
    int result = binsearch(arr, 1, 5);
    printf("test_case_4: %d\n", result);  // Expected: -1
}

// Test case 5: Valid - key at start
void test_case_5() {
    int arr[] = {10, 20, 30};
    int result = binsearch(arr, 3, 10);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Invalid - negative n
void test_case_6() {
    int arr[] = {1, 2, 3};
    int result = binsearch(arr, -2, 2);  // Frama-C should flag this
    // No output check needed
}

// Test case 7: Invalid - unsorted array
void test_case_7() {
    int arr[] = {3, 1, 2};
    int result = binsearch(arr, 3, 2);  // Frama-C should flag this
    // No output check needed
}

// Test case 8: Boundary - empty array
void test_case_8() {
    int arr[] = {0};  // Dummy array for n=0
    int result = binsearch(arr, 0, 5);
    printf("test_case_8: %d\n", result);  // Expected: -1
}

// Test case 9: Boundary - key at end
void test_case_9() {
    int arr[] = {5, 6, 7};
    int result = binsearch(arr, 3, 7);
    printf("test_case_9: %d\n", result);  // Expected: 2
}

// Harness entry point (not main!)
void test_harness_binsearch() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called
}