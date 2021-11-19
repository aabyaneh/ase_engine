uint64_t count(uint64_t* arr, uint64_t value, uint64_t start_position, uint64_t end_position) {
  uint64_t i;
  uint64_t cnt;

  cnt = 0;
  i   = start_position;
  while (i < end_position) {
    if (*(arr + i) == value)
      cnt = cnt + 1;
    i = i + 1;
  }

  return cnt;
}

uint64_t is_permutation(uint64_t* arr1, uint64_t n1, uint64_t* arr2, uint64_t n2) {
  uint64_t i;
  uint64_t count1;
  uint64_t count2;

  if (n1 != n2) return 0;

  i = 0;
  while (i < n1) {
    count1 = count(arr1, *(arr1 + i), 0, i) + 1 + count(arr1, *(arr1 + i), i+1, n1);
    count2 = count(arr2, *(arr1 + i), 0, n2);
    if (count1 != count2)
      return 0;
    i = i + 1;
  }

  return 1;
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t  i;
  uint64_t* arr1;
  uint64_t  cnt1;
  uint64_t* arr2;
  uint64_t  cnt2;
  uint64_t  r;

  cnt1 = 6;
  arr1 = malloc(cnt1 * 8);
  cnt2 = 6;
  arr2 = malloc(cnt2 * 8);

  i = 0;
  while (i < cnt1) {
    interval((arr1 + i), 0, 2*cnt1, 1);
    i = i + 1;
  }

  i = 0;
  while (i < cnt2) {
    interval((arr2 + i), 0, 2*cnt2, 1);
    i = i + 1;
  }

  r = is_permutation(arr1, cnt1, arr2, cnt2);

  return 0;
}