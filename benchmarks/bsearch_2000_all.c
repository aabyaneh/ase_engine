uint64_t compar(uint64_t* op1, uint64_t* op2) {
  if (*op1 < *op2) {
    return 1;
  } else if (*op1 > *op2) {
    return 2;
  } else {
    return 0;
  }
}

uint64_t* bsearch(uint64_t* key, uint64_t* base, uint64_t num, uint64_t size) {
	uint64_t* pivot;
	uint64_t  result;

	while (num != 0) {
		pivot = base + (num / 2) * size;
		result = compar(key, pivot);

		if (result == 0)
			return pivot;

		if (result == 2) {
			base = pivot + size;
			num = num - 1;
		}
		num = num / 2;
	}

	return (uint64_t*) 0;
}

uint64_t main() {
  uint64_t  i;
  uint64_t* arr;
  uint64_t* element;
  uint64_t* res;
  uint64_t  cnt;
  uint64_t  step;

  cnt  = 2000;
  step = 1;
  arr = malloc(cnt * 8);
  i = 0;
  while (i < cnt) {
    interval(arr + i, 0, cnt*2, 1);
    i = i + 1;
  }

  element  = malloc(1 * 8);
  interval(element, 0, cnt*2, 1);

  res = bsearch(element, arr, cnt, 1);

  return 0;
}