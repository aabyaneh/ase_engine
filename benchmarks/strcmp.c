/*
  Function: int strcmp (const char *s1, const char *s2)

  return 0 if equal, 1 if < and 2 otherwise.

  help:  http://www.gnu.org/software/libc/manual/html_mono/libc.html#String_002fArray-Comparison
*/

uint64_t strcmp(uint64_t* s1, uint64_t* s2) {
  while (*s1 == *s2) {
    if (*s1 == 0)
      return 0;
    s1 = s1 + 1;
    s2 = s2 + 1;
  }

  if (*s1 < *s2)
    return 1;
  else
    return 2;
}

uint64_t main() {
  uint64_t* str1;
  uint64_t* str2;
  uint64_t  cmp;

  /*
  symbolic code:
    - input: two character arrays where at most one of them is symbolic.
  */

  str1 = malloc(6 * 8);
  *(str1 + 0) = '/';
  *(str1 + 1) = 'x';
  *(str1 + 2) = 'y';
  *(str1 + 3) = '/';
  *(str1 + 4) = 'r';
  *(str1 + 5) = 0;

  str2 = malloc(6 * 8);
  *(str2 + 0) = '/';
  *(str2 + 1) = 'y';
  *(str2 + 2) = 'y';
  *(str2 + 3) = '/';
  *(str2 + 4) = 'r';
  *(str2 + 5) = 0;

  // return 0 if equal, 1 if < and 2 otherwise.
  cmp = strcmp(str1, str2);

  return 0;
}