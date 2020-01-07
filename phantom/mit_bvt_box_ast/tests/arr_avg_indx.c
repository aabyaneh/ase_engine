/*
  Count pairs in an array that hold i*arr[i] > j*arr[j]
*/

uint64_t count_pair(uint64_t* arr, uint64_t cnt) {
  uint64_t i;
  uint64_t j;
  uint64_t result;

  result = 0;

  i = 0;
  while (i < cnt) {
    j = i + 1;
    while (j < cnt) {
      if ( i * *(arr + i) > j * *(arr + j))
        result = result + 1;
      j = j + 1;
    }
    i = i + 1;
  }

  return result;
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t v1;
  uint64_t cnt;
  uint64_t* arr;

  cnt = 400;
  arr = malloc(cnt * 8);

  // uint64_t arr[] = {5 , 0, 10, 2, 4, 1, 6};

  v1 = 0;
  while (v1 < cnt) {
    *(arr + v1) = cnt - v1;
    v1 = v1 + 1;
  }

  input((arr + cnt/2), 0, 2*cnt-1, 1);

  count_pair(arr, cnt);

  // printf("%llu\n", a);

  return 0;
}