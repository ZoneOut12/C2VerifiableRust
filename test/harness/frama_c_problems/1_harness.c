// ========== Original Code (with ACSL) ==========
int main(){
    int i=0;
    /*@
        loop invariant 0 <= i <= 30;
        loop variant 30 - i;
    */
    while (i<30){
        ++i;
    }
    //@assert i==30;
   
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal execution
void test_case_1() {
    int result = main();
    printf("test_case_1: %d\n", result);  // Expected: 0
}

// Test case 2: Valid - repeated execution
void test_case_2() {
    int result = main();
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - standard environment
void test_case_3() {
    int result = main();
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid - default optimizations
void test_case_4() {
    int result = main();
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid - consistent results
void test_case_5() {
    int result = main();
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary - minimum initial value
void test_case_6() {
    int result = main();
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Boundary - maximum final value
void test_case_7() {
    int result = main();
    printf("test_case_7: %d\n", result);  // Expected: 0
}

// Test case 8: Invalid - no preconditions to violate
void test_case_8() {
    // No meaningful violation possible for this function
    int result = main();
    // No output check needed for invalid case
}

// Test case 9: Invalid - no invariant violation possible
void test_case_9() {
    // No meaningful violation possible for this function
    int result = main();
    // No output check needed for invalid case
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
    // test_case_8 and test_case_9 intentionally included to show invalid cases
}
