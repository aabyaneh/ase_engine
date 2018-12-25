/*
  The bsearch function searches the sorted array array for an object that is equivalent to key. The array contains count elements, each of which is of size size bytes.

  The compare function is used to perform the comparison. This function is called with two pointer arguments and should return an integer less than, equal to, or greater than zero corresponding to whether its first argument is considered less than, equal to, or greater than its second argument. The elements of the array must already be sorted in ascending order according to this comparison function.

  The return value is a pointer to the matching array element, or a null pointer if no match is found. If the array contains more than one element that matches, the one that is returned is unspecified.

  This function derives its name from the fact that it is implemented using the binary search algorithm.

  source code: binutils-2.31/libiberty/bsearch.c
  source code: https://github.com/torvalds/linux/blob/master/lib/bsearch.c
  help:        http://www.gnu.org/software/libc/manual/html_mono/libc.html
*/

uint64_t compar(uint64_t* op1, uint64_t* op2) {
  if (*op1 == *op2)
    return 0;
  else if (*op1 < *op2)
    return 1;
  else
    return 2;
}

uint64_t* bsearch(uint64_t* key, uint64_t* base, uint64_t num, uint64_t size) {
	uint64_t* pivot;
	uint64_t  result;

  // base should be casted to (const char *) so that
  // pointer arithmetic adds one byte each time in (base + (num / 2) * size)
  // but we don't have char type so always size = 1.
	while (num != 0) {
		pivot = base + (num / 2) * size;
		result = compar(key, pivot);

		if (result == 0)
			return pivot;

		if (result == 2) {
			base = pivot + size;
			num = num - 1;
		}
		num = num / 2;
	}

	return (uint64_t*) 0;
}

uint64_t main() {
  uint64_t  i;
  uint64_t* arr;
  uint64_t* element;
  uint64_t* res;

  /*
  symbolic code:
    - length of the array is a fixed concrete value.
    - the array must be sorted.
    - two scenarios are possible:
      1. the item that we would like to search is symbolic, and array's elements are concrete.
      2. the item that we would like to search is concrete, and array's elements are symbolic.
    - scenario number 2 is hard as the array must be sorted (further constraints over
      ordering of array's elements are needed).
  */

  // array should be sorted
  arr = malloc(100 * 8);
  i = 0;
  while (i < 100) {
    *(arr + i) = i;
    i = i + 1;
  }

  element  = malloc(1 * 8);
  *element = 87;
  res = bsearch(element, arr, 100, 1);

  return 0;
}