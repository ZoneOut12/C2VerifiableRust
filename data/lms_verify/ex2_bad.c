/*@ requires n > 0;
    ensures 0 <= \result && \result < n;
    assigns \nothing;
*/
int pick_index(int n) { return 0; }

/*@ 
  requires n > 0;
  requires \valid_read(p + (0..n-1));
  assigns \nothing;
*/
int pick_element(int* p, int n) {
  int i = pick_index(n);
  //@ assert (0 <= i && i < n);
  //@ assert \valid_read(p + (0..n-1));
  return p[i];
}

/*@
  requires \valid_read(p + (0..0));
  ensures \result == p[0];
  assigns \nothing;
*/
int pick_first(int* p) {
  return p[0];
}
