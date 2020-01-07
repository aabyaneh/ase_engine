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

  cnt = 10000;
  arr = malloc(cnt * 8);

  v1 = 0;
  while (v1 < cnt) {
    *(arr + v1) = cnt - v1;
    v1 = v1 + 1;
  }

  input(arr + (cnt/2)  , 0, 2*cnt-1, 1);
  // input(arr + (cnt/2+1), 0, 2*cnt-1, 1);
  // input(arr + (cnt/2+2), 0, 2*cnt-1, 1);

  largest(arr, cnt);

  // v1 = 0;
  // while (v1 < cnt) {
  //   printsv(v1, *(arr+v1));
  //   v1 = v1 + 1;
  // }

  return 0;
}