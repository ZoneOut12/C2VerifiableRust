// ========== Original Code (with ACSL) ==========
#include <stdio.h>
/*@ 
    requires \valid(a+(0..n-1));
    requires n > 0;
    ensures \forall integer i,j; 0<=i<=j<=n-1 ==> a[i]<=a[j];
*/
void bubbleSort(int *a, int n) {
    int i, j, temp;
    /*@ 
        loop invariant \forall integer p,q; i<=p<=q<=n-1 ==> a[p]<=a[q];
        loop invariant \forall integer p,q; 0<=p<i+1==q<=n-1 ==> a[p]<=a[q];
        loop invariant 0<=i<n;
        loop assigns i,j,temp,a[0..n-1];
        loop variant i;
    */
      for(i=n-1; i>0; i--) {
        /*@  loop invariant 0<=j<=i<n;
            loop invariant \forall integer k; 0<=k<=j ==> a[k] <= a[j];
            loop invariant \forall integer p, q; 0<=p<i+1==q<=n-1 ==> a[p]<=a[q];
            loop assigns j,temp,a[0..i];
            loop variant i-j;
        */
        for(j=0; j<i; j++) {
            if (a[j] > a[j+1]) {
                    temp = a[j];
                    a[j] = a[j+1];
                    a[j+1] = temp;
            }
        }
    }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal array
void test_case_1() {
    int arr[] = {3, 1, 4, 1, 5};
    bubbleSort(arr, 5);
    printf("test_case_1: [%d, %d, %d, %d, %d]\n", arr[0], arr[1], arr[2], arr[3], arr[4]);  // Expected: [1, 1, 3, 4, 5]
}

// Test case 2: Valid - already sorted array
void test_case_2() {
    int arr[] = {1, 2, 3, 4};
    bubbleSort(arr, 4);
    printf("test_case_2: [%d, %d, %d, %d]\n", arr[0], arr[1], arr[2], arr[3]);  // Expected: [1, 2, 3, 4]
}

// Test case 3: Valid - reverse sorted array
void test_case_3() {
    int arr[] = {5, 4, 3};
    bubbleSort(arr, 3);
    printf("test_case_3: [%d, %d, %d]\n", arr[0], arr[1], arr[2]);  // Expected: [3, 4, 5]
}

// Test case 4: Valid - array with duplicates
void test_case_4() {
    int arr[] = {2, 2, 1};
    bubbleSort(arr, 3);
    printf("test_case_4: [%d, %d, %d]\n", arr[0], arr[1], arr[2]);  // Expected: [1, 2, 2]
}

// Test case 5: Valid - minimal valid array size (n=2)
void test_case_5() {
    int arr[] = {5, 3};
    bubbleSort(arr, 2);
    printf("test_case_5: [%d, %d]\n", arr[0], arr[1]);  // Expected: [3, 5]
}

// Test case 6: Boundary - minimal array size (n=1)
void test_case_6() {
    int arr[] = {42};
    bubbleSort(arr, 1);
    printf("test_case_6: [%d]\n", arr[0]);  // Expected: [42]
}

// Test case 7: Boundary - equal elements in array
void test_case_7() {
    int arr[] = {7, 7};
    bubbleSort(arr, 2);
    printf("test_case_7: [%d, %d]\n", arr[0], arr[1]);  // Expected: [7, 7]
}

// Test case 8: Invalid - n=0 violates n > 0 precondition
void test_case_8() {
    int arr[] = {1, 2, 3};
    bubbleSort(arr, 0);  // Frama-C should flag this
}

// Test case 9: Invalid - NULL pointer violates array validity
void test_case_9() {
    bubbleSort(NULL, 3);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_bubbleSort() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called - they're for precondition testing
}