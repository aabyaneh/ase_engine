/*
  Function: void* lfind(const void *key, const void *base, size_t *nmemb, size_t size, comparison_fn_t compar)

  The lfind function searches in the array with *nmemb elements of size bytes pointed to by base for an element which matches the one pointed to by key. The function pointed to by compar is used to decide whether two elements match.

  The return value is a pointer to the matching element in the array starting at base if it is found. If no matching element is available NULL is returned.

  source code:
  glibc-2.28/misc/lsearch.c
  https://github.com/lattera/glibc/blob/895ef79e04a953cac1493863bcae29ad85657ee1/misc/lsearch.c

  help:  http://www.gnu.org/software/libc/manual/html_mono/libc.html
*/

uint64_t compar(uint64_t* op1, uint64_t* op2) {
  return (*op1 == *op2);
}

uint64_t* lfind(uint64_t* key, uint64_t* base, uint64_t* nmemb, uint64_t size) {
  uint64_t* result;
  uint64_t  cnt;
  uint64_t  loop;

  result = base;
  cnt    = 0;

  // base should be casted to (const char *) or (const void *) so that
  // pointer arithmetic adds one byte each time in (result + size)
  // but we don't have char type so always size = 1.
  loop = 1;
  while (loop) {
    if (cnt < *nmemb) {
      if (compar(key, result) == 0) {
        result = result + size;
        cnt    = cnt + 1;
      } else
        loop = 0;
    } else
      loop = 0;
  }

  if (cnt < *nmemb)
    return result;
  else
    return (uint64_t*) 0;
}

uint64_t main() {
  uint64_t  i;
  uint64_t* arr;
  uint64_t* element;
  uint64_t* length;
  uint64_t* res;

  /*
  symbolic code:
    - length of the array is a fixed concrete value.
    - two scenarios are possible:
      1. the item that we would like to search is symbolic, and array's elements are concrete.
      2. the item that we would like to search is concrete, and array's elements are symbolic.
  */

  arr = malloc(10 * 8);
  i = 0;
  while (i < 10) {
    *(arr + i) = 10 - i;
    i = i + 1;
  }

  element  = malloc(1 * 8);
  length   = malloc(1 * 8);
  *element = 9;
  *length  = 10;
  res = lfind(element, arr, length, 1);

  return 0;
}