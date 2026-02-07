/* run.config
   STDOPT:+"-wp-timeout 5"
*/

/*@
  inductive even_natural(integer n) {
  case even_nul:
    even_natural(0);
  case even_not_nul_natural:
    \forall integer n ;
      even_natural(n) ==> even_natural(n+2);
  case odd_case_0:
      !even_natural(1);
  case odd_case_n:
    \forall integer n ;
      !even_natural(n) ==> !even_natural(n+2);
  }
*/

void foo(){
  //@ assert even_natural(4);
  //@ assert even_natural(42);
}

void bar(){
  int a = 1 ;
  //@ assert !even_natural(a);
}