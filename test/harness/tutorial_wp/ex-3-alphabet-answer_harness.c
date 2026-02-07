// ========== Original Code (with ACSL) ==========
/*@ assigns \nothing ;
  ensures \result <==> ('a' <= c <= 'z') || ('A' <= c <= 'Z') ;
*/
int alphabet_letter(char c){
  if( ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') ) return 1 ;
  else return 0 ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - lowercase 'a'
void test_case_1() {
    int result = alphabet_letter('a');
    printf("test_case_1: %d\n", result);  // Expected: 1
}

// Test case 2: Valid - lowercase 'z'
void test_case_2() {
    int result = alphabet_letter('z');
    printf("test_case_2: %d\n", result);  // Expected: 1
}

// Test case 3: Valid - uppercase 'A'
void test_case_3() {
    int result = alphabet_letter('A');
    printf("test_case_3: %d\n", result);  // Expected: 1
}

// Test case 4: Valid - uppercase 'Z'
void test_case_4() {
    int result = alphabet_letter('Z');
    printf("test_case_4: %d\n", result);  // Expected: 1
}

// Test case 5: Valid - lowercase 'm'
void test_case_5() {
    int result = alphabet_letter('m');
    printf("test_case_5: %d\n", result);  // Expected: 1
}

// Test case 6: Boundary - lowercase 'a'
void test_case_6() {
    int result = alphabet_letter('a');
    printf("test_case_6: %d\n", result);  // Expected: 1
}

// Test case 7: Boundary - uppercase 'Z'
void test_case_7() {
    int result = alphabet_letter('Z');
    printf("test_case_7: %d\n", result);  // Expected: 1
}

// Test case 8: Invalid - space character
void test_case_8() {
    int result = alphabet_letter(' ');  // Frama-C should flag this (no preconditions)
}

// Test case 9: Invalid - digit '3'
void test_case_9() {
    int result = alphabet_letter('3');  // Frama-C should flag this (no preconditions)
}

// Harness entry point (not main!)
void test_harness_alphabet_letter() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8() and test_case_9() intentionally not called - for precondition testing
}
void test_case_8() {
    char c = '3';
    int result = alphabet_letter(c);
    printf("Test 8: %s\n", result == 0 ? "PASS" : "FAIL");
}

void test_case_9() {
    char c = ' ';
    int result = alphabet_letter(c);
    printf("Test 9: %s\n", result == 0 ? "PASS" : "FAIL");
}