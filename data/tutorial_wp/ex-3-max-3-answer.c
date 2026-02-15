/*@
  predicate one_of{L}(integer i, int *a, int *b, int *c) =
    \exists int* p ; p \in { a, b, c } && \at(*p, L) == i ;
*/

/*@
  requires \valid(a) && \valid(b) && \valid(c) ;
  assigns \nothing ;
  ensures one_of{Pre}(\result, a, b, c);
  ensures \result >= *a && \result >= *b && \result >= *c ;
*/
int max_of(int* a, int* b, int* c){
  if(*a >= *b && *a >= *c) return *a ;
  if(*b >= *a && *b >= *c) return *b ;
  return *c ;
}

typedef int (*binop_t)(int, int);

/*@ requires -1000000 <= a <= 1000000;
    requires -1000000 <= b <= 1000000;
    assigns \nothing;
    ensures \result == a + b;
*/
int op_add(int a, int b)
{
    return a + b;
}

/*@ requires -1000000 <= a <= 1000000;
    requires -1000000 <= b <= 1000000;
    assigns \nothing;
    ensures \result == a - b;
*/
int op_sub(int a, int b)
{
    return a - b;
}

/*@ requires op == &op_add || op == &op_sub;
    requires -1000000 <= a <= 1000000;
    requires -1000000 <= b <= 1000000;
    assigns \nothing;
    ensures op == &op_add ==> \result == a + b;
    ensures op == &op_sub ==> \result == a - b;
*/
int compute(binop_t op, int a, int b)
{
    if (op == &op_add) return op_add(a, b);
    return op_sub(a, b);
}
