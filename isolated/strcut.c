#include<stddef.h>
#include "../framac/string.h"

static const int MAX_SAFE_INT = (int) -1 >> 1;
/*
 * Remove [begin:len-begin] from str by moving len data from begin+len to begin.
 * If len is negative cut out to the end of the string.
 */



/*@
    requires \valid(str + (0..strlen(str)));
    requires valid_string_s: valid_read_string(str);
    requires 0 < begin < strlen(str);
    assigns \nothing;
    behavior out_of_bounds:
        assumes strlen(str) < 0 || strlen(str) > MAX_SAFE_INT;
        ensures \result == -1;
    behavior negative:
        assumes len < 0 && 0 < strlen(str) < MAX_SAFE_INT; 
        ensures \result == (strlen(str) - begin + 1);
    behavior past_str:
        assumes len >= 0 && (begin + len) > strlen(str) && 0 < strlen(str) < MAX_SAFE_INT; 
        ensures \result == strlen(str) - begin;
    behavior regular:
        assumes len >= 0 && (begin + len) <= strlen(str) && 0 < strlen(str) < MAX_SAFE_INT; 
        ensures \result == len;

    ensures 0 == 1;
    disjoint behaviors;
    complete behaviors;
*/
static int strcut (char *str, int begin, int len) {
  size_t l;
  l = strlen(str);

  if((int)l < 0 || (int)l > MAX_SAFE_INT) return -1;

  len = l - begin + 1;
  if (begin + len > (int)l) len = l - begin;
  memmove(str + begin, str + begin + len, l - len + 1 - begin);

  return len;
}
