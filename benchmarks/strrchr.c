uint64_t* strchr(uint64_t* s, uint64_t c) {
  while (1) {
    if (*s == c)
      return s;
    if (*s == 0)
      return (uint64_t*) 0;

    s = s + 1;
  }
}

uint64_t* strrchr(uint64_t* s, uint64_t c) {
  uint64_t* found;
  uint64_t* p;

  if (c == 0)
    return strchr(s, 0);

  found = (uint64_t*) 0;
  p = strchr(s, c);
  while (p != (uint64_t*) 0) {
    found = p;
    s = p + 1;
    p = strchr(s, c);
  }

  return found;
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

  ptr = strrchr(str, '/');

  return 0;
}