uint64_t* strchr(uint64_t* s, uint64_t c) {
  while (1) {
    if (*s == c)
      return s;
    if (*s == 0)
      return (uint64_t*) 0;

    s = s + 1;
  }
}

uint64_t main() {
  uint64_t* str;
  uint64_t* ptr;

  /* code */
  str = malloc(6 * 8);
  *(str + 0) = '/';
  *(str + 1) = 'x';
  *(str + 2) = 'y';
  *(str + 3) = '/';
  *(str + 4) = 'r';
  *(str + 5) = 0;

  ptr = strchr(str, 'y');

  return 0;
}