uint64_t smallest(uint64_t* arr, uint64_t n) {
  uint64_t i;
  uint64_t min;

  min = *arr;

  i = 1;
  while (i < n) {
    if (*(arr + i) < min)
      min = *(arr + i);
    i = i + 1;
  }

  return min;
}

uint64_t largest(uint64_t* arr, uint64_t n) {
  uint64_t i;
  uint64_t max;

  max = *arr;

  i = 1;
  while (i < n) {
    if (*(arr + i) > max)
      max = *(arr + i);
    i = i + 1;
  }

  return max;
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t v1;
  uint64_t cnt;
  uint64_t* arr;
  uint64_t r1;
  uint64_t r2;

  cnt = 10;
  arr = malloc(cnt * 8);

  v1 = 0;
  while (v1 < cnt) {
    interval(arr + v1, 0, 2*cnt, 1);
    v1 = v1 + 1;
  }

  r1 = smallest(arr, cnt);
  r2 = largest (arr, cnt);

  return 0;
}