// ========== Original Code (with ACSL) ==========
int unknown();

/*@ requires n > 0; */
void foo(int n) {
  int c = 0;
  /*@ loop invariant n != c;
      loop invariant c >= 0 && c <= n;
      loop invariant c > n ==> c == n;
      loop invariant c > n ==> c == n + 1;
      loop invariant c <= n;
      loop invariant \forall integer k; 1 <= k <= c ==> (\exists integer i; 1 <= i <= n && i == c);
      loop invariant 0 <= c;
      loop assigns n;
      loop assigns c;
  */
  while (unknown()) {
    if (unknown()) {
      if (c > n) {
        c = c + 1;
      }
    } else {
      if (c == n) {
        c = 1;
      }
    }
  }
  if (c < 0) {
    if (c > n) {
      //@ assert c == n;
    }
  }
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid input n=3
void test_case_1() {
    foo(3);
    printf("test_case_1 completed\n");
}

// Test case 2: Valid input n=4
void test_case_2() {
    foo(4);
    printf("test_case_2 completed\n");
}

// Test case 3: Valid input n=5
void test_case_3() {
    foo(5);
    printf("test_case_3 completed\n");
}

// Test case 4: Valid input n=10
void test_case_4() {
    foo(10);
    printf("test_case_4 completed\n");
}

// Test case 5: Valid input n=7
void test_case_5() {
    foo(7);
    printf("test_case_5 completed\n");
}

// Test case 6: Boundary case n=1
void test_case_6() {
    foo(1);
    printf("test_case_6 completed\n");
}

// Test case 7: Boundary case n=2
void test_case_7() {
    foo(2);
    printf("test_case_7 completed\n");
}

// Test case 8: Invalid input n=0
void test_case_8() {
    foo(0);
    printf("test_case_8 completed\n");
}

// Test case 9: Invalid input n=-1
void test_case_9() {
    foo(-1);
    printf("test_case_9 completed\n");
}

// Harness entry point
void test_harness_foo() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called for invalid cases
}
void test_case_1() { foo(5); }
void test_case_2() { foo(10); }
void test_case_3() { foo(2); }
void test_case_4() { foo(100); }
void test_case_5() { foo(3); }
void test_case_6() { foo(1); }
void test_case_7() { foo(2147483647); }
void test_case_8() { foo(0); }
void test_case_9() { foo(-42); }