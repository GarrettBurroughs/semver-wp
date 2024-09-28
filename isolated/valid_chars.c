#include <stddef.h>
#include "../framac/string.h"



/*@
    axiomatic Contains {
        logic integer contains(char c, char* matrix, integer len) reads matrix[0..len-1];
        axiom contains_true:
            \forall char c, char* matrix, size_t len;
            (\exists size_t i; 0 <= i < len && matrix[i] == c) ==> contains(c, matrix, len) == 1;
        axiom contains_false:
            \forall char c, char* matrix, size_t len;
            (\forall size_t i; 0 <= i < len ==> matrix[i] != c) ==> contains(c, matrix, len) == 0;
    }
*/




/*@
    requires \valid_read(matrix + (0 .. len - 1));
    terminates \true;
    exits \false;
    assigns \nothing;
    ensures \result == contains(c, matrix, len);
  */
static int contains(const char c, const char *matrix, size_t len);
/*@
    requires \valid(str + (0..strlen(str)));
    requires \valid(matrix + (0..strlen(matrix)));
    requires valid_string_s: valid_read_string(str);
    requires valid_string_m: valid_read_string(matrix);

    behavior valid:
        assumes !\exists size_t i ; 0 <= i < strlen(str) && contains(str[i], matrix, strlen(matrix)) == 0;
        ensures \result == 1;
    behavior not_valid: 
        assumes \exists size_t i ; 0 <= i < strlen(str) && contains(str[i], matrix, strlen(matrix)) == 0;
        ensures \result == 0;

    disjoint behaviors;
    complete behaviors;
 */
static int has_valid_chars (const char *str, const char *matrix) {
  size_t i, len, mlen;
  len = strlen(str);
  mlen = strlen(matrix);

  /*@
        loop invariant 0 <= i <= len;
        loop invariant \forall size_t j; 0 <= j < i ==> contains(str[j], matrix, mlen) != 0;
        loop assigns i;
        loop variant len - i;
    */
  for (i = 0; i < len; i++)
    if (contains(str[i], matrix, mlen) == 0)
      return 0;

  return 1;
}
