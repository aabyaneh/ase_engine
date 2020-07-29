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
  uint64_t n;
  uint64_t m;
  uint64_t k;
  uint64_t i;
  uint64_t j;
  uint64_t cnt;

  cnt = 50;
  interval(&n, 0, cnt, 1);
  interval(&m, 0, cnt, 1);
  k = 0;

  interval(&i, 0, 5, 1);
  while (i < n) {
    j = 0;
    while (j < m) {
      k = k + 1;
      j = j + 1;
    }
    i = i + 1;
  }

  VERIFIER_assert(k <= cnt*cnt);

  return 0;
}