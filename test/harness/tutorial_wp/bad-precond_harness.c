/*@ requires a < 0 && a > 0;
  ensures \false;
*/
void foo(int a){

}

#include <stdio.h>

// Test case 1: Invalid - negative value
void test_case_1() {
    foo(-5);  // Violates a > 0
}

// Test case 2: Invalid - positive value
void test_case_2() {
    foo(5);  // Violates a < 0
}

// Test case 3: Invalid - zero value
void test_case_3() {
    foo(0);  // Violates both conditions
}

// Test case 4: Invalid - negative edge case
void test_case_4() {
    foo(-1);  // Violates a > 0
}

// Test case 5: Invalid - positive edge case
void test_case_5() {
    foo(1);  // Violates a < 0
}

// Test case 6: Invalid - large negative value
void test_case_6() {
    foo(-100);  // Violates a > 0
}

// Test case 7: Invalid - large positive value
void test_case_7() {
    foo(100);  // Violates a < 0
}

void test_harness_foo() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
}
void test_case_1() { foo(5); }
void test_case_2() { foo(-3); }
void test_case_3() { foo(0); }
void test_case_4() { foo(100); }
void test_case_5() { foo(-1); }
void test_case_6() { foo(42); }
void test_case_7() { foo(-999); }