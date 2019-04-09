uint64_t* malloc(uint64_t size);

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

  /* create temp arrays */
  L = malloc(n1 * 8);
  R = malloc(n2 * 8);

  /* Copy data to temp arrays L[] and R[] */
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

  /* Merge the temp arrays back into arr[l..r]*/
  i = 0; // Initial index of first subarray
  j = 0; // Initial index of second subarray
  k = l; // Initial index of merged subarray
  loop = 1;
  while (loop) {
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

  // Copy the remaining elements of L[], if there are any
  while (i < n1) {
    *(arr + k) = *(L + i);
    i = i + 1;
    k = k + 1;
  }

  // Copy the remaining elements of R[], if there are any
  while (j < n2) {
    *(arr + k) = *(R + j);
    j = j + 1;
    k = k + 1;
  }
}

// l is for left index and r is right index of the sub-array of arr to be sorted
void mergeSort(uint64_t* arr, uint64_t l, uint64_t r) {
  uint64_t m;

  if (l < r) {
    // Same as (l+r)/2, but avoids overflow for large l and h
    m = l + (r-l)/2;

    // Sort first and second halves
    mergeSort(arr, l, m);
    mergeSort(arr, m+1, r);

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
    if (v1 != cnt/2)
      *(arr + v1) = cnt - v1;
    v1 = v1 + 1;
  }

  *(arr + cnt/2) = input(0, 2*cnt-1, 1);

  mergeSort(arr, 0, cnt - 1);

  return 0;
}