// ========== Original Code (with ACSL) ==========
/* run.config
   STDOPT:+"-wp-timeout 5"
*/

enum note { N500, N200, N100, N50, N20, N10, N5, N2, N1 };
int const values[] = { 500, 200, 100, 50, 20, 10, 5, 2, 1 };

/*@
  requires N500 <= n <= N1;
  requires \valid(rest) && *rest >= 0 ;
  assigns *rest;
  ensures \result == \old(*rest)/values[n];
  ensures \old(*rest) == *rest + \result * values[n] ;
*/
int remove_max_notes(enum note n, int* rest){
  int num = (*rest)/values[n];
  (*rest) -= num * values[n];
  return num;
}

/*@
  requires \valid(change+(0..8));
  requires amount >= 0 && received >= 0;
  assigns  change[0 .. 8];

  behavior not_enough:
    assumes amount > received ;
    ensures \result == -1;

  behavior change:
    assumes amount <= received ;
    ensures \result == 0;
    ensures
      received - amount ==
          change[N500] * values[N500]
        + change[N200] * values[N200]
        + change[N100] * values[N100]
        + change[N50]  * values[N50]
        + change[N20]  * values[N20]
        + change[N10]  * values[N10]
        + change[N5]   * values[N5]
        + change[N2]   * values[N2]
        + change[N1]   * values[N1];
    ensures
         change[N1]   * values[N1]   < values[N2]
      && change[N2]   * values[N2]   < values[N5]
      && change[N5]   * values[N5]   < values[N10]
      && change[N10]  * values[N10]  < values[N20]
      && change[N20]  * values[N20]  < values[N50]
      && change[N50]  * values[N50]  < values[N100]
      && change[N100] * values[N100] < values[N200]
      && change[N200] * values[N200] < values[N500];

  complete behaviors;
  disjoint behaviors;
*/
int make_change(int amount, int received, int change[9]){
  if(amount > received) return -1;

  int rest = received - amount ;

  change[N500] = remove_max_notes(N500, &rest);
  change[N200] = remove_max_notes(N200, &rest);
  change[N100] = remove_max_notes(N100, &rest);
  change[N50]  = remove_max_notes(N50,  &rest);
  change[N20]  = remove_max_notes(N20,  &rest);
  change[N10]  = remove_max_notes(N10,  &rest);
  change[N5]   = remove_max_notes(N5,   &rest);
  change[N2]   = remove_max_notes(N2,   &rest);
  change[N1]   = remove_max_notes(N1,   &rest);

  return 0;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - amount > received
void test_case_1() {
    int change[9];
    int result = make_change(150, 100, change);
    printf("test_case_1: %d\n", result);  // Expected: -1
}

// Test case 2: Valid - exact payment
void test_case_2() {
    int change[9];
    int result = make_change(50, 50, change);
    printf("test_case_2: %d\n", result);  // Expected: 0
}

// Test case 3: Valid - typical change calculation
void test_case_3() {
    int change[9];
    int result = make_change(323, 500, change);
    printf("test_case_3: %d\n", result);  // Expected: 0
}

// Test case 4: Boundary - maximum note
void test_case_4() {
    int change[9];
    int result = make_change(0, 500, change);
    printf("test_case_4: %d\n", result);  // Expected: 0
}

// Test case 5: Valid - small change
void test_case_5() {
    int change[9];
    int result = make_change(97, 100, change);
    printf("test_case_5: %d\n", result);  // Expected: 0
}

// Test case 6: Boundary - change just below highest note
void test_case_6() {
    int change[9];
    int result = make_change(499, 500, change);
    printf("test_case_6: %d\n", result);  // Expected: 0
}

// Test case 7: Valid (New) - All denominations used
// Change sum: 500+200+100+50+20+10+5+2+1 = 888
void test_case_7() {
    int change[9];
    // Expected: 0 as result, and change array should have exactly one of each note
    int result = make_change(0, 888, change);
    printf("test_case_7: %d\n", result);  // Expected: 0
    
    // The following are the expected values for each index:
    // change[N500]=1, change[N200]=1, change[N100]=1, change[N50]=1, 
    // change[N20]=1, change[N10]=1, change[N5]=1, change[N2]=1, change[N1]=1
}

// Test case 8: Invalid - NULL change array
void test_case_8() {
    int *change = NULL;
    int result = make_change(50, 100, change);  // Frama-C should flag this
}

// Test case 9: Invalid - negative amount
void test_case_9() {
    int change[9];
    int result = make_change(-10, 100, change);  // Frama-C should flag this
}

// Harness entry point (not main!)
void test_harness_make_change() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    test_case_6();
    test_case_7();
    // test_case_8 and test_case_9 intentionally not called - for precondition testing
}

void test_harness_valid_remove_max_notes() {
    int rest;
    int result;

    // --- Test Case 1: Standard case - amount is perfectly divisible ---
    rest = 1000;
    // Expected: 1000 / 500 = 2, rest = 0
    result = remove_max_notes(N500, &rest);
    printf("Valid 1: result=%d, rest=%d\n", result, rest);

    // --- Test Case 2: Standard case - partial removal with remainder ---
    rest = 350;
    // Expected: 350 / 100 = 3, rest = 50
    result = remove_max_notes(N100, &rest);
    printf("Valid 2: result=%d, rest=%d\n", result, rest);

    // --- Test Case 3: Amount is less than the note value ---
    rest = 15;
    // Expected: 15 / 20 = 0, rest = 15
    result = remove_max_notes(N20, &rest);
    printf("Valid 3: result=%d, rest=%d\n", result, rest);

    // --- Test Case 4: Initial amount is exactly zero ---
    rest = 0;
    // Expected: 0 / 50 = 0, rest = 0
    result = remove_max_notes(N50, &rest);
    printf("Valid 4: result=%d, rest=%d\n", result, rest);

    // --- Test Case 5: Testing smallest denomination ---
    rest = 7;
    // Expected: 7 / 1 = 7, rest = 0
    result = remove_max_notes(N1, &rest);
    printf("Valid 5: result=%d, rest=%d\n", result, rest);

    // --- Test Case 6: Amount exactly equals note value ---
    rest = 200;
    // Expected: 200 / 200 = 1, rest = 0
    result = remove_max_notes(N200, &rest);
    printf("Valid 6: result=%d, rest=%d\n", result, rest);

    // --- Test Case 7: Large amount with high-value notes ---
    rest = 2300;
    // Expected: 2300 / 500 = 4, rest = 300
    result = remove_max_notes(N500, &rest);
    printf("Valid 7: result=%d, rest=%d\n", result, rest);
}

void test_harness_invalid_remove_max_notes() {
    // --- Test Case 8: Violates \valid(rest) ---
    // Passing a NULL pointer. WP should flag the 'requires \valid(rest)' violation.
    int *rest_null = NULL;
    // result = remove_max_notes(N100, rest_null); 

    // --- Test Case 9: Violates *rest >= 0 ---
    // Passing a pointer to a negative value. WP should flag the '*rest >= 0' violation.
    int rest_neg = -100;
    remove_max_notes(N50, &rest_neg);
}