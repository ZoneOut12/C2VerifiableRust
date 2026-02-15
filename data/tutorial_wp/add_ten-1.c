/*@
  requires 0 <= a <= 100 ;
  ensures \result == \old(a) + 10;
*/
int add_ten(int a){
  /*@
    loop invariant 0 <= i <= 10;
    loop invariant a == \at(a, Pre) + i; //< ADDED
    loop assigns i, a;
    loop variant 10 - i;
  */
  for (int i = 0; i < 10; ++i)
    ++a;

  return a;
}

typedef int (*int_transform)(int);

/*@ requires 0 <= a <= 1000000;
    assigns \nothing;
    ensures \result == a + a;
*/
int double_val(int a)
{
    return a + a;
}

/*@ requires -1000000 <= a <= 1000000;
    assigns \nothing;
    ensures \result == -a;
*/
int negate_val(int a)
{
    return -a;
}

/*@ requires f == &double_val || f == &negate_val;
    requires f == &double_val ==> 0 <= a <= 1000000;
    requires f == &negate_val ==> -1000000 <= a <= 1000000;
    assigns \nothing;
    ensures f == &double_val ==> \result == a + a;
    ensures f == &negate_val ==> \result == -a;
*/
int apply_transform(int_transform f, int a)
{
    if (f == &double_val) return double_val(a);
    return negate_val(a);
}
