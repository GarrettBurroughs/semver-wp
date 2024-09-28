

typedef struct semver_version_s {
  int major;
  int minor;
  int patch;
  char * metadata;
  char * prerelease;
} semver_t;


/*@
    behavior gt:
        assumes x > y;
        ensures \result == 1;
    behavior lt:
        assumes x < y;
        ensures \result == -1;
    behavior eq:
        assumes x == y;
        ensures \result == 0;

    disjoint behaviors;
    complete behaviors;
*/
static int
binary_comparison (int x, int y) {
  if (x == y) return 0;
  if (x > y) return 1;
  return -1;
}




/*@ 
    
    behavior major_gt:
        assumes x.major > y.major;
        ensures \result == 1;

    behavior major_lt:
        assumes x.major < y.major;
        ensures \result == -1;
    
    behavior minor_gt:
        assumes x.major == y.major && x.minor > y.minor;
        ensures \result == 1;

    behavior minor_lt:
        assumes x.major == y.major && x.minor < y.minor;
        ensures \result == -1;

    behavior patch_gt:
        assumes x.major == y.major && x.minor == y.minor && x.patch > y.patch;
        ensures \result == 1;

    behavior patch_lt:
        assumes x.major == y.major && x.minor == y.minor && x.patch < y.patch;
        ensures \result == -1;

    behavior eq:
        assumes x.major == y.major && x.minor == y.minor && x.patch == y.patch;
        ensures \result == 0;

    disjoint behaviors;
    complete behaviors;
*/
int
semver_compare_version (semver_t x, semver_t y) {
  int res;

  if ((res = binary_comparison(x.major, y.major)) == 0) {
    if ((res = binary_comparison(x.minor, y.minor)) == 0) {
      return binary_comparison(x.patch, y.patch);
    }
  }

  return res;
}
