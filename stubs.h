#define size_t unsigned long
#include "framac/__fc_string_axiomatic.h"

/*@
    requires \valid(str)
 */
unsigned long strlen(const char* str);

/*@
    requires \valid_read(src + (0 .. n - 1))
    requires \valid(dest + (0 .. n - 1))
    assigns dest + (0 .. n - 1)
    ensures \forall size_t i; 0 <= i < n ==> src[i] == dest[i];
 */
void *memmove(void *dest, const void *src, size_t n);

/*@
    requires \valid_read(s)
    ensures s[\result] == c
*/
char *strchr(const char *s, int c) noexcept(true);

long strtol(const char * nptr, char **endptr, int base);

void *calloc(size_t nmemb, size_t size);

void *memcpy(void *dest, const void *src, size_t n);

char *strcpy(char *dest, const char *src);

void free(void *ptr);

int strncmp(const char *s1, const char *s2, size_t n);

int sprintf(char *str, const char *format, ...);

char *strcat(char *dest, const char *src);

void *memset(void *s, int c, size_t n);

