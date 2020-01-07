void  VERIFIER_error() {
  uint64_t x;
  x = 10 / 0;
}

void VERIFIER_assert(uint64_t cond) {
  if (cond == 0) {
    VERIFIER_error();
  }
  return;
}

uint64_t main() {
  uint64_t n;
  uint64_t x;
  uint64_t y;

  input(&n, 0, 200, 1); // input(0, -1, 1);
  x = n;
  y = 0;

  while(x > 0) {
    x = x - 1;
    y = y + 1;
  }

  VERIFIER_assert(y == n);
}

