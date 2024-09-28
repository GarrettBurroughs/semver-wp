
typedef struct semver_version_s {
  int major;
  int minor;
  int patch;
  char * metadata;
  char * prerelease;
} semver_t;

/**
 * Version bump helpers
 */

/*@
    requires \valid(x);

    ensures x->major == \old(x->major) + 1;
  */
void
semver_bump (semver_t *x) {
  x->major++;
}

/*@
    requires \valid(x);

    ensures x->minor == \old(x->minor) + 1;
  */
void
semver_bump_minor (semver_t *x) {
  x->minor++;
}

/*@
    requires \valid(x);

    ensures x->patch == \old(x->patch) + 1;
  */
void
semver_bump_patch (semver_t *x) {
  x->patch++;
}
