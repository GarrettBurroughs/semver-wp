#define DELIMITER    "."
#define PR_DELIMITER "-"
#define MT_DELIMITER "+"
#include <stddef.h>
#include "../framac/string.h"

#define SLICE_SIZE   50

typedef struct semver_version_s {
  int major;
  int minor;
  int patch;
  char * metadata;
  char * prerelease;
} semver_t;

/*@
    requires \valid(str + (0..strlen(str)));
    requires \valid(sep + (0..strlen(sep)));


    ensures \valid(str + (0..strlen(str) + 1 + strlen(sep)));
  */
static void
concat_num (char * str, int x, char * sep);

/*@
    requires \valid(str + (0..strlen(str)));
    requires \valid(sep + (0..strlen(sep)));
    requires \valid(x + (0..strlen(x)));


    ensures \valid(str + (0..strlen(str) + strlen(x) + strlen(sep)));
  */
static void
concat_char (char * str, char * x, char * sep);

/*@
    requires \valid(x);
    requires \valid(dest)
    requires \valid(x->prerelease + (0 + strlen(x->prerelease)));
    requires \valid(x->metadata + (0 + strlen(x->metadata)));


  */
void semver_render (semver_t *x, char *dest) {
  if (x->major) concat_num(dest, x->major, NULL);
  if (x->minor) concat_num(dest, x->minor, DELIMITER);
  if (x->patch) concat_num(dest, x->patch, DELIMITER);
  if (x->prerelease) concat_char(dest, x->prerelease, PR_DELIMITER);
  if (x->metadata) concat_char(dest, x->metadata, MT_DELIMITER);
}
