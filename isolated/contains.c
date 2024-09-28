#include <stddef.h>

/*@
    requires \valid_read(matrix + (0 .. len - 1));
    assigns \nothing;
    behavior in:
        assumes ! \forall size_t i ; 0 <= i < len ==> matrix[i] != c;
        ensures \result == 1;
    behavior out:
        assumes \forall size_t i ; 0 <= i < len ==> matrix[i] != c;
        ensures \result == 0;
    disjoint behaviors;
    complete behaviors;
  */
static int contains(const char c, const char *matrix, size_t len) {
  /*@
        loop invariant 0 <= x <= len;
        loop invariant \forall size_t i; 0 <= i < x ==> matrix[i] != c;
        loop assigns x;
        loop variant len - x;
   */
  for (size_t x = 0; x < len; x++)
    if (matrix[x] == c)
      return 1;
  return 0;
}
