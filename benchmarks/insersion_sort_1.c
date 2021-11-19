void insertion_sort(uint64_t* arr, uint64_t n) {
   uint64_t i;
   uint64_t key;
   uint64_t j;
   uint64_t saved_j;

   i = 1;
   while (i < n) {
     key = *(arr + i);
     j = i;

     saved_j = 0;
     while (j > 0) {
       if (*(arr + j - 1) > key) {
         *(arr + j) = *(arr + j - 1);
         j = j - 1;
       } else {
         saved_j = j;
         j = 0;
       }
     }

     if (saved_j > 0)
      j = saved_j;
     *(arr + j) = key;

     i = i + 1;
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

  insertion_sort(arr, cnt);

  return 0;
}