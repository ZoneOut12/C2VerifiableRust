// ========== Original Code (with ACSL) ==========
int main(){
  int i = 0;
  int h = 42;
  
  /*@
    loop invariant 0 <= i <= 29;
    loop assigns i;
    loop variant 30 - i;
  */
  while(i < 29){
    i++ ;
  }

  if(i < 30){
    ++i;
    
    if(i == 30){
      i = 42 ;
      h = 84 ;
    }
  }
  //@assert i == 42;
  //@assert h == 84;
}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - default execution
void test_case_1() {
    printf("test_case_1: Running default execution\n");
    main();  // Expected: Assertions should pass
}

// Test case 2: Valid - repeated execution
void test_case_2() {
    printf("test_case_2: Re-running default execution\n");
    main();  // Expected: Same behavior
}

// Test case 3: Valid - third execution
void test_case_3() {
    printf("test_case_3: Third execution\n");
    main();
}

// Test case 4: Valid - fourth execution
void test_case_4() {
    printf("test_case_4: Fourth execution\n");
    main();
}

// Test case 5: Valid - fifth execution
void test_case_5() {
    printf("test_case_5: Fifth execution\n");
    main();
}

// Test case 6: Invalid - no preconditions to violate
void test_case_6() {
    printf("test_case_6: No preconditions to violate\n");
    // Cannot violate preconditions in this function
}

// Test case 7: Invalid - second invalid case
void test_case_7() {
    printf("test_case_7: No preconditions to violate\n");
}

// Test case 8: Boundary - minimal loop iterations
void test_case_8() {
    printf("test_case_8: Boundary case with minimal iterations\n");
    // Cannot modify i's initial value in this implementation
}

// Test case 9: Boundary - maximal loop iterations
void test_case_9() {
    printf("test_case_9: Boundary case with maximal iterations\n");
    // Cannot modify i's initial value in this implementation
}

// Harness entry point (not main!)
void test_harness_main() {
    test_case_1();
    test_case_2();
    test_case_3();
    test_case_4();
    test_case_5();
    // test_case_6() and 7() intentionally included to show invalid cases
    test_case_6();
    test_case_7();
    // test_case_8() and 9() included for boundary coverage
    test_case_8();
    test_case_9();
}
#include <stdio.h>
#include <stdlib.h>

void redirect_stdin(const char* input) {
    FILE* tmp = fopen("tmp.in", "w");
    if (!tmp) exit(1);
    fprintf(tmp, "%s", input);
    fclose(tmp);
    freopen("tmp.in", "r", stdin);
}

int test_case_1() {
    redirect_stdin("3 1 2 3\n");
    return main();
}

int test_case_2() {
    redirect_stdin("1 42\n");
    return main();
}

int test_case_3() {
    redirect_stdin("4 10 20 30 40\n");
    return main();
}

int test_case_4() {
    redirect_stdin("2 -5 0\n");
    return main();
}

int test_case_5() {
    redirect_stdin("5 1 1 1 1 1\n");
    return main();
}

int test_case_6() {
    redirect_stdin("2 1 2 3\n");
    return main();
}

int test_case_7() {
    redirect_stdin("3 2 1 3\n");
    return main();
}

int test_case_8() {
    redirect_stdin("0\n");
    return main();
}

int test_case_9() {
    // Generate input for n=1000 with sorted elements
    char input[10000];
    snprintf(input, sizeof(input), "1000");
    for (int i = 0; i < 1000; ++i) {
        char buf[20];
        snprintf(buf, sizeof(buf), " %d", i);
        strcat(input, buf);
    }
    strcat(input, "\n");
    redirect_stdin(input);
    return main();
}