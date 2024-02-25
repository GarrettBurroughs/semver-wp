#define size_t unsigned long
#define NULL ((void*)0)

unsigned long strlen(const char* str);

void *memmove(void *dest, const void *src, size_t n);

char *strchr(const char *s, int c);

long strtol(const char * nptr, char **endptr, int base);

void *calloc(size_t nmemb, size_t size);

void *memcpy(void *dest, const void *src, size_t n);

char *strcpy(char *dest, const char *src);

void free(void *ptr);

int strncmp(const char *s1, const char *s2, size_t n);

int sprintf(char *str, const char *format, ...);

char *strcat(char *dest, const char *src);

void *memset(void *s, int c, size_t n);

