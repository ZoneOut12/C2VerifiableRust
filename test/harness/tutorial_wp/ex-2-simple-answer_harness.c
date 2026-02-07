// ========== Original Code (with ACSL) ==========
enum Kind { VOWEL, CONSONANT };

/*@
  requires 'a' <= c <= 'z' ;
  assigns \nothing;
  behavior vowel:
    assumes c \in { 'a', 'e', 'i', 'o', 'u', 'y' };
    ensures \result == VOWEL;
  behavior consonant:
    assumes ! (c \in { 'a', 'e', 'i', 'o', 'u', 'y' });
    ensures \result == CONSONANT;
  complete behaviors;
  disjoint behaviors;
*/
enum Kind kind_of_letter(char c){
  if(c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y')
    return VOWEL;
  else
    return CONSONANT;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid vowel 'a'
void test_case_1() {
    enum Kind result = kind_of_letter('a');
    printf("test_case_1: %d\n", result);  // Expected: 0 (VOWEL)
}

// Test case 2: Valid consonant 'b'
void test_case_2() {
    enum Kind result = kind_of_letter('b');
    printf("test_case_2: %d\n", result);  // Expected: 1 (CONSONANT)
}

// Test case 3: Valid vowel 'u'
void test_case_3() {
    enum Kind result = kind_of_letter('u');
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Valid consonant 'z'
void test_case_4() {
    enum Kind result = kind_of_letter('z');
    printf("test_case_4: %d\n", result);  // Expected: 1
}

// Test case 5: Valid vowel 'y'
void test_case_5() {
    enum Kind result = kind_of_letter('y');
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Invalid uppercase 'A'
void test_case_6() {
    enum Kind result = kind_of_letter('A');  // Frama-C should flag this
}

// Test case 7: Invalid symbol '#'
void test_case_7() {
    enum Kind result = kind_of_letter('#');  // Frama-C should flag this
}

// Test case 8: Boundary 'a'
void test_case_8() {
    enum Kind result = kind_of_letter('a');
    printf("test_case_8: %d\n", result);  // Expected: 0
}

// Test case 9: Boundary 'z'
void test_case_9() {
    enum Kind result = kind_of_letter('z');
    printf("test_case_9: %d\n", result);  // Expected: 1
}

// Harness entry point
void test_harness_kind_of_letter() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // test_case_6 and test_case_7 intentionally not called - invalid cases
    test_case_8();
    test_case_9();
}