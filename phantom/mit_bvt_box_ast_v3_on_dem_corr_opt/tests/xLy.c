/*
  x < y pairs
*/

uint64_t get_pairs(uint64_t* arr, uint64_t n) {
  uint64_t i;
  uint64_t j;
  uint64_t count;

  // To store the number of valid pairs
  count = 0;
  i = 0;
  while (i < n) {
    j = 0;
    while (j < n) {
      if (i != j)
        if (*(arr + i) < *(arr + j))
          count = count + 1;
      j = j + 1;
    }
    i = i + 1;
  }

  // Return the count of valid pairs
  return count;
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t v1;
  uint64_t cnt;
  uint64_t* arr;

  cnt = 100;
  arr = malloc(cnt * 8);

  v1 = 0;
  while (v1 < cnt) {
    *(arr + v1) = cnt * v1;
    v1 = v1 + 1;
  }

  // input((arr + cnt/2), 0, 2*cnt-1, 1);
  // input((arr + cnt/4), 0, 2*cnt-1, 1);

  input((arr + 90), 0, 2*cnt-1, 1);
  input((arr + 91), 0, 2*cnt-1, 1);
  input((arr + 92), 0, 2*cnt-1, 1);
  input((arr + 93), 0, 2*cnt-1, 1);
  // input((arr + 4), 0, 2*cnt-1, 1);
  // input((arr + 5), 0, 2*cnt-1, 1);

  get_pairs(arr, cnt);

  return 0;
}