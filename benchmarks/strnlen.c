uint64_t strnlen(uint64_t* s, uint64_t maxlen) {
	uint64_t len;
  uint64_t loop;

  loop = 1;
  len = 0;
  while (loop) {
    if (len < maxlen) {
      if (*s == 0)
        loop = 0;
      else {
        len = len + 1;
        s = s + 1;
      }
    } else
      loop = 0;
  }

	return len;
}

uint64_t main() {
  uint64_t* str;
  uint64_t  len;
  
  str = malloc(16 * 8);
  *(str + 0)  = '/';
  *(str + 1)  = 'x';
  *(str + 2)  = 'y';
  *(str + 3)  = '/';
  *(str + 4)  = 'r';
  *(str + 5)  = '/';
  *(str + 6)  = 'x';
  *(str + 7)  = 'y';
  *(str + 8)  = '/';
  *(str + 9)  = 'r';
  *(str + 10) = 'r';
  *(str + 11) = 'r';
  *(str + 12) = 'r';
  *(str + 13) = 'r';
  *(str + 14) = 'r';
  *(str + 15) = 0;

  len = strnlen(str, 20);

  return 0;
}