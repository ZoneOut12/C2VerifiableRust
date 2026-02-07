#include <limits.h>

/*@ 
  requires INT_MIN <= x+y <= INT_MAX ;
  ensures  \result == x + y ;
*/
int add(int x, int y){
  return x+y ;
}

#include <stdio.h>

// Test case 1: Valid - normal inputs
void test_case_1() {
    int result = add(5, 10);
    printf("test_case_1: %d\n", result);
}

// Test case 2: Valid - larger numbers
void test_case_2() {
    int result = add(100, 200);
    printf("test_case_2: %d\n", result);
}

// Test case 3: Valid - negative numbers
void test_case_3() {
    int result = add(-5, -10);
    printf("test_case_3: %d\n", result);
}

// Test case 4: Valid - sum at INT_MAX
void test_case_4() {
    int result = add(INT_MAX - 1, 1);
    printf("test_case_4: %d\n", result);
}

// Test case 5: Valid - sum at INT_MIN
void test_case_5() {
    int result = add(INT_MIN + 1, -1);
    printf("test_case_5: %d\n", result);
}

// Test case 6: Boundary - x at INT_MAX
void test_case_6() {
    int result = add(INT_MAX, 0);
    printf("test_case_6: %d\n", result);
}

// Test case 7: Boundary - x at INT_MIN
void test_case_7() {
    int result = add(INT_MIN, 0);
    printf("test_case_7: %d\n", result);
}

// Test case 8: Invalid - overflow
void test_case_8() {
    int result = add(INT_MAX, 1);
}

// Test case 9: Invalid - underflow
void test_case_9() {
    int result = add(INT_MIN, -1);
}

void test_harness_add() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
}