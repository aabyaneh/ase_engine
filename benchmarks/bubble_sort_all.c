void swap(uint64_t* xp, uint64_t* yp) {
  uint64_t temp;

  temp = *xp;
  *xp = *yp;
  *yp = temp;
}

void bubbleSort(uint64_t* arr, uint64_t n) {
   uint64_t i;
   uint64_t j;
   uint64_t swapped;

   i = 0;
   while (i < n - 1) {
     swapped = 0;
     j = 0;
     while (j < n-i-1) {
       if (*(arr + j) > *(arr + (j + 1))) {
         swap(arr + j, arr + (j + 1));
         swapped = 1;
       }
       j = j + 1;
     }

     i = i + 1;

     if (swapped == 0)
      i = n; // break
   }
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t v1;
  uint64_t cnt;
  uint64_t* arr;

  cnt = 8;
  arr = malloc(cnt * 8);

  v1 = 0;
  while (v1 < cnt) {
    interval(arr + v1, 0, 2*cnt, 1);
    v1 = v1 + 1;
  }

  bubbleSort(arr, cnt);

  return 0;
}