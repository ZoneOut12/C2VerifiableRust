// ========== Original Code (with ACSL) ==========
int main(){
  int i = 0;
  int h = 42;
  
  /*@
    loop invariant 0 <= i <= 30;
    loop assigns i;
    loop variant 30 - i;
  */
  while(i < 30){
    ++i;

    if(i == 30) break ;
  }
  //@assert i == 30;
  //@assert h == 42;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal execution
void test_case_1() {
    int result = main();
    printf("test_case_1: Completed\n");
}

// Test case 2: Valid - repetition
void test_case_2() {
    int result = main();
    printf("test_case_2: Completed\n");
}

// Test case 3: Valid - repetition
void test_case_3() {
    int result = main();
    printf("test_case_3: Completed\n");
}

// Test case 4: Valid - repetition
void test_case_4() {
    int result = main();
    printf("test_case_4: Completed\n");
}

// Test case 5: Valid - repetition
void test_case_5() {
    int result = main();
    printf("test_case_5: Completed\n");
}

// Test case 6: Invalid - no preconditions to violate
void test_case_6() {
    printf("test_case_6: No precondition violation possible\n");
}

// Test case 7: Invalid - no preconditions to violate
void test_case_7() {
    printf("test_case_7: No precondition violation possible\n");
}

// Test case 8: Boundary - loop terminates at i=30
void test_case_8() {
    int result = main();
    printf("test_case_8: Completed\n");
}

// Test case 9: Boundary - initial values i=0, h=42
void test_case_9() {
    int result = main();
    printf("test_case_9: Completed\n");
}

// Harness entry point (not main!)
void test_harness_main() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    test_case_8();
    test_case_9();
}
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

// Simulate stdin input for test cases
void setup_input(int n, int* arr) {
    FILE* input = fopen("test_input.txt", "w");
    fprintf(input, "%d", n);
    for (int i = 0; i < n; i++) {
        fprintf(input, " %d", arr[i]);
    }
    fclose(input);
    freopen("test_input.txt", "r", stdin);
}

void test_case_1() {
    int arr[] = {1, 2, 3};
    setup_input(3, arr);
    int result = main();
    assert(result == 0);
}

void test_case_2() {
    int arr[] = {-5, 0};
    setup_input(2, arr);
    int result = main();
    assert(result == 0);
}

void test_case_3() {
    int arr[] = {42};
    setup_input(1, arr);
    int result = main();
    assert(result == 0);
}

void test_case_4() {
    setup_input(0, NULL);
    int result = main();
    assert(result == 0);
}

void test_case_5() {
    int arr[] = {10, 20, 30, 40};
    setup_input(4, arr);
    int result = main();
    assert(result == 0);
}

void test_case_6() {
    int arr[] = {3, 1, 2};
    setup_input(3, arr);
    int result = main();
    assert(result == -1);
}

void test_case_7() {
    int arr[] = {5, 3};
    setup_input(2, arr);
    int result = main();
    assert(result == -1);
}

void test_case_8() {
    int arr[] = {1, 1, 1, 1, 1};
    setup_input(5, arr);
    int result = main();
    assert(result == 0);
}

void test_case_9() {
    int arr[] = {5, 4, 3, 2};
    setup_input(4, arr);
    int result = main();
    assert(result == -1);
}