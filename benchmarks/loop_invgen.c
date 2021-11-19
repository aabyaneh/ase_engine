void VERIFIER_error() {
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
  uint64_t l;
  uint64_t n;
  uint64_t m;
  uint64_t k;
  uint64_t i;

  interval(&n, 0, 9, 1);
  interval(&l, 0, 9, 1);

  if (l <= 0) return 0;

  k = 1;
  while (k < n) {
    i = l;
    while (i < n) {
      VERIFIER_assert( 1 <= i );
      i = i + 1;
    }
    interval(&m, 0, 10, 1);
    if (m > 0) {
      l = l + 1;
    }

    k = k + 1;
  }

  return 0;
}