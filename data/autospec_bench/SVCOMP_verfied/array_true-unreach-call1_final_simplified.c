#include "assert.h"

void main() {
  int A[2048];
  int i;

  /*@
  loop invariant \forall integer j; 0 <= j < i ==> A[j] == j;
  loop invariant 0 <= i <= 1024;
  loop assigns i;
  loop assigns A[0..1023];
  loop variant 1024 - i; 
  */
  for (i = 0; i < 1024; i++) {
    A[i] = i;
  }

  //@ assert A[1023] == 1023;
}