/*
  This file is a C* implementation of equality/disequality comparison of array's elements
  written by Alireza Abyaneh.
*/

uint64_t cmp(uint64_t* arr, uint64_t cnt) {
  uint64_t i;
  uint64_t j;
  uint64_t t;

  i = 0;
  while (i < cnt) {
    j = 0;
    while (j < i) {
      if (*(arr + i) == *(arr + j))
        return 1;

      j = j + 1;
    }
    i = i + 1;
  }

  return 0;
}

uint64_t main() {
  uint64_t cnt;
  uint64_t v;
  uint64_t res;
  uint64_t* arr;

  cnt = 260;

  arr = malloc(cnt * 8);

  v = 0;
  while (v < cnt) {
    *(arr + v) = input(0, 255, 1); // read(1, (arr + v), 1);
    v = v + 1;
  }

  res = cmp(arr, cnt);

  return 0;
}