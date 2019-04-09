uint64_t UINT64_MAX_T = -1;

uint64_t atoi(uint64_t* s) {
  uint64_t n;
  uint64_t c;

  n = 0;
  c = *s;

  // loop until s is terminated
  while (c != 0) {
    c = c - '0';

    if (c > 9) {
      // cannot convert non-decimal number
      // error
      return n;
    }

    // use base 10 but detect wrap around
    if (n < UINT64_MAX_T / 10)
      n = n * 10 + c;
    else if (n == UINT64_MAX_T / 10)
      if (c <= UINT64_MAX_T % 10)
        n = n * 10 + c;
      else {
        // s contains a decimal number larger than UINT64_MAX
        // error
        return n;
      }
    else {
      // s contains a decimal number larger than UINT64_MAX
      // error
      return n;
    }

    s = s + 1;
    c = *s;
  }

  return n;
}

uint64_t main() {
  uint64_t* str;
  uint64_t  int_val;

  str = malloc(6 * 8);
  *(str + 0) = '3';
  *(str + 1) = '4';
  *(str + 2) = '7';
  *(str + 3) = '8';
  *(str + 4) = '1';
  *(str + 5) = 0;

  int_val = atoi(str);

  return 0;
}