// ========== Original Code (with ACSL) ==========
#include <stddef.h>

/*@ ensures min <= \result <= max; */
size_t random_between(size_t min, size_t max);

void random_loop(size_t bound){
  /*@ loop invariant 0 <= i <= bound ;
      loop assigns i;
      loop variant i;
  */
  for(size_t i = bound; i > 0; ){
    i -= random_between(1, i);
  }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - bound = 2
void test_case_1() {
    random_loop(2);
}

// Test case 2: Valid - bound = 3
void test_case_2() {
    random_loop(3);
}

// Test case 3: Valid - bound = 5
void test_case_3() {
    random_loop(5);
}

// Test case 4: Valid - bound = 10
void test_case_4() {
    random_loop(10);
}

// Test case 5: Valid - bound = 100
void test_case_5() {
    random_loop(100);
}

// Test case 6: Invalid - bound = -1
void test_case_6() {
    random_loop(-1);
}

// Test case 7: Invalid - bound = -5
void test_case_7() {
    random_loop(-5);
}

// Test case 8: Boundary - bound = 0
void test_case_8() {
    random_loop(0);
}

// Test case 9: Boundary - bound = 1
void test_case_9() {
    random_loop(1);
}

// Harness entry point (not main!)
void test_harness_random_loop() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_8();
    test_case_9();
    // test_case_6 and test_case_7 intentionally not called
}
void test_case_1() { random_loop(5); }
void test_case_2() { random_loop(10); }
void test_case_3() { random_loop(0); }
void test_case_4() { random_loop(100); }
void test_case_5() { random_loop(42); }
void test_case_6() { random_loop(-1); }
void test_case_7() { random_loop(-10); }
void test_case_8() { random_loop(0); }
void test_case_9() { random_loop(2147483647); }