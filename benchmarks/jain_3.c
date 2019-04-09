uint64_t main() {
  uint64_t x;
  uint64_t y;
  uint64_t i;
  uint64_t a;
  uint64_t r;

  x = 1;
  y = 1;
  a = input(0, -1, 1);

  i = 0;
  while(i < 10000) {
    x = x + 2 * input(0, -1, 1);
    y = y + 2 * input(0, -1, 1);

    if (x + y != 1) {
      r = a/x;
    } else {
      r = x/a;
    }

    i = i + 1;
  }

  return r;
}
