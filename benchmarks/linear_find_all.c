uint64_t compar(uint64_t* op1, uint64_t* op2) {
  return (*op1 == *op2);
}

uint64_t* lfind(uint64_t* key, uint64_t* base, uint64_t* nmemb, uint64_t size) {
  uint64_t* result;
  uint64_t  cnt;
  uint64_t  loop;

  result = base;
  cnt    = 0;

  loop = 1;
  while (loop > 0) {
    if (cnt < *nmemb) {
      if (compar(key, result) == 0) {
        result = result + size;
        cnt    = cnt + 1;
      } else
        loop = 0;
    } else
      loop = 0;
  }

  if (cnt < *nmemb)
    return result;
  else
    return (uint64_t*) 0;
}

uint64_t main() {
  uint64_t  i;
  uint64_t* arr;
  uint64_t* element;
  uint64_t* length;
  uint64_t* res;
  uint64_t  cnt;
  uint64_t  step;

  cnt  = 1000;
  step = 1;

  arr = malloc(cnt * 8);
  i = 0;
  while (i < cnt) {
    interval(arr+i, 0, (cnt+1)*2, 1);
    i = i + 1;
  }

  element  = malloc(1 * 8);
  interval(element, 0, (cnt+1)*2, 1);

  length   = malloc(1 * 8);
  *length  = cnt;

  res = lfind(element, arr, length, 1);

  return 0;
}