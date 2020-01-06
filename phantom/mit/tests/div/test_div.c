uint64_t main() {
  uint64_t a;
  uint64_t b;

  a = input(11, 27, 4); // a = <11, 27, 4>
  b = a / 2;            // b = <5, 13, 2>
  printsv(1, b);
  if (5 < b) {
    // b = <7, 13, 2>
    // a = <15, 27, 4>
    printsv(2, b);
    printsv(3, a);
    if (a >= 15) {
      // a = <15, 27, 4>
      // b = <7, 13, 2>
      printsv(4, a);
      printsv(5, b);
    }
  } else {
    // b = <5, 5, 2>
    // a = <11, 11, 4>
    printsv(6, b);
    printsv(7, a);
  }
}