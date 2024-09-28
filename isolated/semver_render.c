#define DELIMITER    "."
#define PR_DELIMITER "-"
#define MT_DELIMITER "+"
#include <stddef.h>
#include "../framac/string.h"

typedef struct semver_version_s {
  int major;
  int minor;
  int patch;
  char * metadata;
  char * prerelease;
} semver_t;

/*@ 
     axiomatic IntToAscii {
        logic char* itoa{L}(integer n);
        
        axiom valid_char{L}: \forall integer i ; 0 <= i < 10 ==> \valid(itoa(i));

        axiom to_ascii{L}: \forall integer i ; 0 <= i < 10 ==> *itoa(i) == i - 48;
     }
*/

/*
    requires \valid(str);
    requires \valid_read(sep);
    
    behavior no_sep:
        assumes sep == NULL;
        ensures str == \old(str) ^ x;
    behavior sep:
        assumes sep != NULL;
        ensures 

    disjoint behaviors;
    complete behaviors;
  */
static void concat_num (char * str, int x, char * sep);

/*@ 
   predicate str_concat(char* result, char* a, char* b) = \forall size_t i ; 0 <= i < strlen(result) ==> i < strlen(a) ? result[i] == a[i] : result[i] == b[i - strlen(a)];
  */

/*@ 
   predicate str_concat_char(char* result, char* a, char b, char* c) = 
    \forall size_t i ; 0 <= i < strlen(result) ==> 
        i < strlen(a) ? result[i] == a[i] : 
            i == strlen(a) ? result[i] == b : result[i] == c[(i - strlen(a) + 1)];
  */

/*@ 
   predicate len_test(char* result) = strlen(result) == 5;
  */

/*@
    requires valid_string_src: valid_read_string(src);
    requires valid_string_dest: valid_string(dest);
    requires room_string: \valid(dest + (0 .. strlen(dest) + strlen(src)));

    ensures \forall size_t i ; 0 <= i < strlen(dest) ==> i < strlen(\old(dest)) ? dest[i] == \old(dest)[i] : dest[i] == src[i - strlen(src)];

 */
void test(char *dest, char *src) {
    /* strcat(dest, src); */
}


/*@
    requires valid_string_x: valid_read_string(x);
    requires valid_string_sep: valid_read_string(sep);
    requires valid_string_str: valid_string(str);
    requires \valid(str + (0 .. strlen(str) + strlen(x) + strlen(sep) ));

    behavior no_sep:
        assumes sep == NULL;

    behavior sep:
        assumes sep != NULL;

    disjoint behaviors;
    complete behaviors;

*/
static void concat_char (char * str, char * x, char * sep);

/**
 * Render a given semver as string
 */

/*@ 
    requires \valid(x)
    requires \valid(dest)
  */
void semver_render (semver_t *x, char *dest) {
  if (x->major) concat_num(dest, x->major, NULL);
  if (x->minor) concat_num(dest, x->minor, DELIMITER);
  if (x->patch) concat_num(dest, x->patch, DELIMITER);
  if (x->prerelease) concat_char(dest, x->prerelease, PR_DELIMITER);
  if (x->metadata) concat_char(dest, x->metadata, MT_DELIMITER);
}
