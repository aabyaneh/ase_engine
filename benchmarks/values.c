uint64_t main() {
  uint64_t n;
  uint64_t m;
  uint64_t k;
  uint64_t cnt;

  cnt = 100;
  interval(&n, 0, cnt, 1);
  interval(&m, 0, cnt, 1);
  interval(&k, 0, cnt, 1);

  if (n < cnt / 2) {
    printsv(1, n);
    printsv(2, m);
    printsv(3, k);
    if (n < m) {
      printsv(4, n);
      printsv(5, m);
      printsv(6, k);
      if (m % 3 < cnt / 3) {
        printsv(7, n);
        printsv(8, m);
        printsv(9, k);
      }
    }
  }

  return 0;
}