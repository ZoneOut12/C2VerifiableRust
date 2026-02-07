/*@
  requires \valid(a) && \valid(b);
  assigns  *a, *b ;

  behavior reorder:
    assumes *a < *b ;
    ensures *a == \old(*b) && *b == \old(*a) ;

  behavior do_not_change:
    assumes *a >= *b ;
    ensures *a == \old(*a) && *b == \old(*b) ;

  complete behaviors ;
  disjoint behaviors ;
*/
void max_ptr(int* a, int* b){
  if(*a < *b){
    int tmp = *b ;
    *b = *a ;
    *a = tmp ;
  }
}

extern int h ;

int main(){
  h = 42 ;

  int a = 24 ;
  int b = 42 ;

  max_ptr(&a, &b) ;

  //@ assert a == 42 && b == 24 ;
  //@ assert h == 42 ;
}

void test_harness_valid_max_ptr() {
    int a, b;

    // --- Test Case 1: Trigger 'reorder' behavior (a < b) ---
    a = 10; b = 20;
    max_ptr(&a, &b);
    // Expected: a = 20, b = 10
    printf("Valid 1: a=%d, b=%d\n", a, b);

    // --- Test Case 2: Trigger 'do_not_change' behavior (a > b) ---
    a = 30; b = 15;
    max_ptr(&a, &b);
    // Expected: a = 30, b = 15
    printf("Valid 2: a=%d, b=%d\n", a, b);

    // --- Test Case 3: Trigger 'do_not_change' behavior (a == b) ---
    a = 42; b = 42;
    max_ptr(&a, &b);
    // Expected: a = 42, b = 42
    printf("Valid 3: a=%d, b=%d\n", a, b);

    // --- Test Case 4: Negative values reordering (a < b) ---
    a = -50; b = -10;
    max_ptr(&a, &b);
    // Expected: a = -10, b = -50
    printf("Valid 4: a=%d, b=%d\n", a, b);

    // --- Test Case 5: Zero and negative comparison ---
    a = -1; b = 0;
    max_ptr(&a, &b);
    // Expected: a = 0, b = -1
    printf("Valid 5: a=%d, b=%d\n", a, b);

    // --- Test Case 6: Boundary values (INT_MIN and INT_MAX) ---
    a = INT_MIN; b = INT_MAX;
    max_ptr(&a, &b);
    // Expected: a = INT_MAX, b = INT_MIN
    printf("Valid 6: a=%d, b=%d\n", a, b);

    // --- Test Case 7: Verification of 'do_not_change' with high values ---
    a = 100; b = 99;
    max_ptr(&a, &b);
    // Expected: a = 100, b = 99
    printf("Valid 7: a=%d, b=%d\n", a, b);
}

void test_harness_invalid_max_ptr() {
    // --- Test Case 8: Violates \valid(a) ---
    // Passing a NULL pointer as the first argument
    int b8 = 42;
    // max_ptr(NULL, &b8); 

    // --- Test Case 9: Violates \valid(b) ---
    // Passing an uninitialized/invalid memory address
    int a9 = 24;
    int *invalid_ptr = (int *)0x123; 
    // max_ptr(&a9, invalid_ptr);
}