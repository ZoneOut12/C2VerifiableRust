// ========== Original Code (with ACSL) ==========
enum Kind { LOWER, UPPER, DIGIT, OTHER } ;

/*@
  assigns \nothing ;
  ensures \result <==> 'a' <= c <= 'z' ;
*/
int is_lower_alpha(char c){
  return 'a' <= c && c <= 'z' ;
}

/*@
  assigns \nothing ;
  ensures \result <==> 'A' <= c <= 'Z' ;
*/
int is_upper_alpha(char c){
  return 'A' <= c && c <= 'Z' ;
}

/*@
  assigns \nothing ;
  ensures \result <==> '0' <= c <= '9' ;
*/
int is_digit(char c){
  return '0' <= c && c <= '9' ;
}

/*@
  assigns \nothing ;
  behavior lower:
    assumes 'a' <= c <= 'z' ;
    ensures \result == LOWER ;

  behavior upper:
    assumes 'A' <= c <= 'Z' ;
    ensures \result == UPPER ;

  behavior digit:
    assumes '0' <= c <= '9' ;
    ensures \result == DIGIT ;

  behavior other:
    assumes ! ('a' <= c <= 'z') ;
    assumes ! ('A' <= c <= 'Z') ;
    assumes ! ('0' <= c <= '9') ;
    ensures \result == OTHER ;

  complete behaviors ;
  disjoint behaviors ;
*/
enum Kind character_kind(char c){
  if(is_lower_alpha(c)) return LOWER ;
  if(is_upper_alpha(c)) return UPPER ;
  if(is_digit(c))       return DIGIT ;
  return OTHER ;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - lowercase 'a'
void test_case_1() {
    char c = 'a';
    enum Kind result = character_kind(c);
    printf("test_case_1: %d\n", result);  // Expected: 0 (LOWER)
}

// Test case 2: Valid - uppercase 'Z'
void test_case_2() {
    char c = 'Z';
    enum Kind result = character_kind(c);
    printf("test_case_2: %d\n", result);  // Expected: 1 (UPPER)
}

// Test case 3: Valid - digit '5'
void test_case_3() {
    char c = '5';
    enum Kind result = character_kind(c);
    printf("test_case_3: %d\n", result);  // Expected: 2 (DIGIT)
}

// Test case 4: Valid - special character '@'
void test_case_4() {
    char c = '@';
    enum Kind result = character_kind(c);
    printf("test_case_4: %d\n", result);  // Expected: 3 (OTHER)
}

// Test case 5: Valid - lowercase 'm'
void test_case_5() {
    char c = 'm';
    enum Kind result = character_kind(c);
    printf("test_case_5: %d\n", result);  // Expected: 0 (LOWER)
}

// Test case 6: Boundary - lowercase 'z'
void test_case_6() {
    char c = 'z';
    enum Kind result = character_kind(c);
    printf("test_case_6: %d\n", result);  // Expected: 0 (LOWER)
}

// Test case 7: Boundary - uppercase 'A'
void test_case_7() {
    char c = 'A';
    enum Kind result = character_kind(c);
    printf("test_case_7: %d\n", result);  // Expected: 1 (UPPER)
}

// Test case 8: Invalid - EOF (-1)
void test_case_8() {
    char c = -1;
    enum Kind result = character_kind(c);
    // No output check needed for invalid case
}

// Test case 9: Invalid - DEL character (127)
void test_case_9() {
    char c = 127;
    enum Kind result = character_kind(c);
    // No output check needed for invalid case
}

// Harness entry point (not main!)
void test_harness_character_kind() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and 9 intentionally not called - for precondition testing
}
void test_case_8() {
    assert(character_kind('A') == LETTER);
}
void test_case_9() {
    assert(character_kind('0') == DIGIT);
}