uint64_t* malloc(uint64_t size);

uint64_t* power_of_two_table;
uint64_t  INT64_MIN_T;

uint64_t signed_less_than(uint64_t a, uint64_t b) {
  return a + INT64_MIN_T < b + INT64_MIN_T;
}

void swap(uint64_t* a, uint64_t* b) {
  uint64_t t;

  t  = *a;
  *a = *b;
  *b = t;
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

void quickSort(uint64_t* arr, uint64_t low, uint64_t high) {
  uint64_t pi;

  if (signed_less_than(low, high)) {
    pi = partition(arr, low, high);

    quickSort(arr, low, pi - 1);
    quickSort(arr, pi + 1, high);
  }
}

void init() {
  uint64_t i;

  // powers of two table with CPUBITWIDTH entries for 2^0 to 2^(CPUBITWIDTH - 1)
  power_of_two_table = malloc(64 * 8);

  *power_of_two_table = 1; // 2^0 == 1

  i = 1;

  while (i < 64) {
    // compute powers of two incrementally using this recurrence relation
    *(power_of_two_table + i) = *(power_of_two_table + (i - 1)) * 2;

    i = i + 1;
  }
}

uint64_t two_to_the_power_of(uint64_t p) {
  // assert: 0 <= p < CPUBITWIDTH
  return *(power_of_two_table + p);
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t v1;
  uint64_t cnt;
  uint64_t* arr;

  init();
  INT64_MIN_T = two_to_the_power_of(63);

  cnt = 300;
  arr = malloc(cnt * 8);

  v1 = 0;
  while (v1 < cnt) {
    if (v1 != cnt/2)
      *(arr + v1) = cnt - v1;
    v1 = v1 + 1;
  }

  *(arr + cnt/2) = input(0, 2*cnt-1, 1);

  quickSort(arr, 0, cnt - 1);

  return 0;
}