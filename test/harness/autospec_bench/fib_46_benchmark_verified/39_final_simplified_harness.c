// ========== Original Code (with ACSL) ==========
int __BLAST_NONDET;
int MAXPATHLEN;

/*
 * "NetBSD_loop_int" from InvGen benchmark suite
 */

int main()
{

  int buf_off;
  int pattern_off;
  int bound_off;

  int glob3_pathbuf_off;
  int glob3_pathend_off;
  int glob3_pathlim_off;
  int glob3_pattern_off;
  int glob3_dc;

  if(MAXPATHLEN > 0); else goto END;

  buf_off = 0;
  pattern_off = 0;

  bound_off = 0 + (MAXPATHLEN + 1) - 1;

  glob3_pathbuf_off = buf_off;
  glob3_pathend_off = buf_off;
  glob3_pathlim_off = bound_off;
  glob3_pattern_off = pattern_off;

  glob3_dc = 0;
  /*@
  loop assigns pattern_off;
  loop assigns glob3_pattern_off;
  loop assigns glob3_pathlim_off;
  loop assigns glob3_pathend_off;
  loop assigns glob3_pathbuf_off;
  loop assigns glob3_dc;
  loop assigns buf_off;
  loop assigns bound_off;
  loop assigns __BLAST_NONDET;
  loop assigns MAXPATHLEN;
  */
  for (;;)
    if (glob3_pathend_off + glob3_dc >= glob3_pathlim_off) break;
    else {
      glob3_dc++;
      //@ assert 0 <= glob3_dc;
      //@ assert glob3_dc < MAXPATHLEN + 1;
      if (__BLAST_NONDET) goto END;
    }
 END:  return 0;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - MAXPATHLEN = 1
void test_case_1() {
    MAXPATHLEN = 1;
    __BLAST_NONDET = 0;
    int result = main();
    printf("test_case_1: %d\n", result);
}

// Test case 2: Valid - MAXPATHLEN = 5
void test_case_2() {
    MAXPATHLEN = 5;
    __BLAST_NONDET = 0;
    int result = main();
    printf("test_case_2: %d\n", result);
}

// Test case 3: Valid - MAXPATHLEN = 10
void test_case_3() {
    MAXPATHLEN = 10;
    __BLAST_NONDET = 0;
    int result = main();
    printf("test_case_3: %d\n", result);
}

// Test case 4: Valid - MAXPATHLEN = 100
void test_case_4() {
    MAXPATHLEN = 100;
    __BLAST_NONDET = 0;
    int result = main();
    printf("test_case_4: %d\n", result);
}

// Test case 5: Valid - MAXPATHLEN = 32767
void test_case_5() {
    MAXPATHLEN = 32767;
    __BLAST_NONDET = 0;
    int result = main();
    printf("test_case_5: %d\n", result);
}

// Test case 6: Invalid - MAXPATHLEN = 0
void test_case_6() {
    MAXPATHLEN = 0;
    __BLAST_NONDET = 0;
    int result = main();
}

// Test case 7: Invalid - MAXPATHLEN = -10
void test_case_7() {
    MAXPATHLEN = -10;
    __BLAST_NONDET = 0;
    int result = main();
}

// Test case 8: Boundary - MAXPATHLEN = 1
void test_case_8() {
    MAXPATHLEN = 1;
    __BLAST_NONDET = 0;
    int result = main();
    printf("test_case_8: %d\n", result);
}

// Test case 9: Boundary - MAXPATHLEN = 2
void test_case_9() {
    MAXPATHLEN = 2;
    __BLAST_NONDET = 0;
    int result = main();
    printf("test_case_9: %d\n", result);
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
int MAXPATHLEN;  // Global variable to satisfy precondition

// Test case functions will set MAXPATHLEN before calling main()