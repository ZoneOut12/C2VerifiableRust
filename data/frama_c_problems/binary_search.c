/*@ requires n >= 0;
    requires \valid(base + (0 .. n-1));
    requires \forall integer k1, integer k2; 0 <= k1 < k2 < n ==> base[k1] <= base[k2];
    
    assigns \nothing;
    ensures \result >= -1 && \result < n;

    behavior present:
        assumes \exists integer k ; 0 <= k < n && base[k] == key ;
        ensures base[\result] == key ;

    behavior not_present:
        assumes \forall integer k ; 0 <= k < n ==> base[k] != key ;
        ensures \result == -1;

    disjoint behaviors;
    complete behaviors;
 */
int binsearch(int *base, int n, int key)
{
   int l = 0;
   int h = n - 1;

   /*@ loop invariant 0 <= l;
       loop invariant h < n;
       loop invariant \forall integer i; 0 <= i < n && base[i] == key ==> l <= i <= h;
       loop assigns l, h;
       loop variant h - l;
    */
   while (l <= h) {
      // INCORRECT: int m = (h + l) / 2;
      int m = l + (h - l) / 2;
      int val = base[m];

      if (val < key) {
         l = m + 1;
         //@ assert \forall integer k1, integer k2; 0 <= k1 < k2 < l ==> base[k1] <= base[k2];
         //@ assert base[m] < key && m == l - 1;
      } else if (val > key) {
         h = m - 1;
      } else {
         //@ assert \forall integer i; 0 <= i < n && base[i] == key ==> l <= i <= h;
         return m;
      }
   }

   return -1;
}