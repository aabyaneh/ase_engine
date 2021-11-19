void merge(uint64_t* arr, uint64_t l, uint64_t m, uint64_t r) {
  uint64_t i;
  uint64_t j;
  uint64_t k;
  uint64_t n1;
  uint64_t n2;
  uint64_t loop;
  uint64_t* L;
  uint64_t* R;

  n1 = m - l + 1;
  n2 = r - m;

  L = malloc(n1 * 8);
  R = malloc(n2 * 8);

  i = 0;
  while (i < n1) {
    *(L + i) = *(arr + (l+i));
    i = i + 1;
  }

  j = 0;
  while (j < n2) {
    *(R + j) = *(arr + (m+j+1));
    j = j + 1;
  }

  i = 0;
  j = 0;
  k = l;
  loop = 1;
  while (loop > 0) {
    if (i < n1) {
      if (j < n2) {
        if (*(L + i) <= *(R + j)) {
          *(arr + k) = *(L + i);
          i = i + 1;
        } else {
          *(arr + k) = *(R + j);
          j = j + 1;
        }

        k = k + 1;
      } else {
        loop = 0;
      }
    } else {
      loop = 0;
    }
  }

  while (i < n1) {
    *(arr + k) = *(L + i);
    i = i + 1;
    k = k + 1;
  }

  while (j < n2) {
    *(arr + k) = *(R + j);
    j = j + 1;
    k = k + 1;
  }
}

void merge_sort(uint64_t* arr, uint64_t l, uint64_t r) {
  uint64_t m;

  if (l < r) {
    m = l + (r-l)/2;

    merge_sort(arr, l, m);
    merge_sort(arr, m+1, r);

    merge(arr, l, m, r);
  }
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t v1;
  uint64_t cnt;
  uint64_t* arr;

  cnt = 300;
  arr = malloc(cnt * 8);

  v1 = 0;
  while (v1 < cnt) {
    *(arr + v1) = cnt - v1;
    v1 = v1 + 1;
  }

  interval((arr + cnt/2), 0, -1, 1);

  merge_sort(arr, 0, cnt - 1);

  return 0;
}