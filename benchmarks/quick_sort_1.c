uint64_t  INT64_MIN_T;

uint64_t signed_less_than(uint64_t a, uint64_t b) {
  return a + INT64_MIN_T < b + INT64_MIN_T;
}

void swap(uint64_t* op1, uint64_t* op2) {
  uint64_t temp;

  temp = *op1;
  *op1 = *op2;
  *op2 = temp;
}

uint64_t partition(uint64_t* arr, uint64_t low, uint64_t high) {
  uint64_t pivot;
  uint64_t i;
  uint64_t j;

  pivot = *(arr + high);
  i     = low - 1;

  j = low;
  while (j < high) {
    if (*(arr + j) <= pivot) {
      i = i + 1;
      swap(arr + i, arr + j);
    }
    j = j + 1;
  }

  swap(arr + i + 1, arr + high);

  return i + 1;
}

void quick_sort(uint64_t* arr, uint64_t low, uint64_t high) {
  uint64_t pi;

  if (signed_less_than(low, high)) {
    pi = partition(arr, low, high);

    quick_sort(arr, low, pi - 1);
    quick_sort(arr, pi + 1, high);
  }
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t v1;
  uint64_t cnt;
  uint64_t* arr;

  INT64_MIN_T = 9223372036854775808;

  cnt = 300;
  arr = malloc(cnt * 8);

  v1 = 0;
  while (v1 < cnt) {
    *(arr + v1) = cnt - v1;
    v1 = v1 + 1;
  }

  interval((arr + cnt/2), 0, -1, 1);

  quick_sort(arr, 0, cnt - 1);

  return 0;
}