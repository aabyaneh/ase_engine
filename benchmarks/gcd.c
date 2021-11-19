uint64_t gcd(uint64_t a, uint64_t b) {
  if (a == 0)
    return b;
  if (b == 0)
    return a;

  if (a < b)
    return gcd(a, b-a);
  else if (a > b)
    return gcd(a-b, b);
  else // a == b
    return a;
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t a;
  uint64_t b;
  uint64_t r;

  interval(&a, 0, 25, 1);
  interval(&b, 0, 25, 1);

  r = gcd(a, b);

  return 0;
}