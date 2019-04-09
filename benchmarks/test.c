uint64_t main() {
  uint64_t a;
  uint64_t b;
  uint64_t c;
  uint64_t d;
  uint64_t* p;

  p = malloc(8*10);
  printsv(0, p);
  a = input(0, 100, 2);
  printsv(1, a);
  if (p == a - 10) {
    printsv(2, a);
  } else {
    printsv(3, a);
  }

  p = malloc(8*10);
  printsv(0, p);
  a = input(0, 100, 2);
  printsv(1, a);
  if (p < a - 10) {
    printsv(2, a);
  } else {
    printsv(3, a);
  }

  a = input(0, 100, 2);
  printsv(0, a);
  b = a + 1;
  printsv(0, b);
  if (a - 10 < 50) {
    printsv(1, a); // 10, 58
    printsv(2, b); // 11, 59
  } else {
    printsv(3, a); // 60, 100; 0, 8
    printsv(4, b); // 61, 101; 1, 9
    if (b * 2 < 150) {
      printsv(5, a); // 60, 72; 0, 8
      printsv(6, b); // 61, 73; 1, 9
    } else {
      printsv(7, a); // 74, 100
      printsv(8, b); // 75, 101
    }
  }

  a = input(9223372036854775808, -1, 1);
  if (a * 2 < -1) {
    printsv(1, a);
  } else {
    printsv(2, a);
  }

  a = input(9223372036854775809, 15372286728091293014, 1);
  if (a * 3 < 9223372036854775811) {
    printsv(1, a);
  } else {
    printsv(2, a);
  }

  a = input(0, 100, 2);
  printsv(0, a);
  b = a + 1;
  printsv(0, b);
  if (a * 4 < 50) {
    printsv(1, a);
    printsv(2, b);
  } else {
    printsv(3, a);
    printsv(4, b);
  }

  a = input(0, 100, 2);
  printsv(0, a);
  b = a + 1;
  printsv(0, b);
  if (a * 4 < 50) {
    printsv(1, a); // 0, 12
    printsv(2, b); // 1, 13
    if (b - 3 < 10) {
      printsv(5, a); // 2, 10
      printsv(6, b); // 3, 11
    } else {
      printsv(8, a); // 12, 12; 0, 0
      printsv(9, b); // 13, 13; 1, 1
    }
  } else {
    printsv(3, a); // 14, 100
    printsv(4, b); // 15, 101
  }

  a = input(0, 100, 2);
  printsv(0, a);
  c = input(0, 50, 3);
  b = a + 1;
  printsv(0, b);
  if (a * 4 < 50) {
    printsv(1, a); // 0, 12
    printsv(2, b); // 1, 13
    b = c + 5;  // 5 , 53
    if (b - 9 < 10) { // -4, 44
      printsv(5, a); // 0, 12
      printsv(6, b); // 11, 17
    } else {
      printsv(8, a); // 0, 12
      printsv(9, b); // 20, 53; 5, 8
    }
  } else {
    printsv(3, a); // 14, 100
    printsv(4, b); // 15, 101
  }

  a = input(0, 100, 2);
  printsv(0, a);
  c = input(0, 50, 3);
  b = a + 1;
  printsv(0, b);
  if (a * 4 == 48) {
    printsv(1, a); // 12, 12
    printsv(2, b); // 13, 13
    b = c + 5;
    if (b - 9 != 10) { // -4, 44
      printsv(5, a); // 12, 12
      printsv(6, b); // 5, 53
    } else {
      printsv(8, a);
      printsv(9, b);
    }
  } else {
    printsv(3, a); // 0, 10; 14, 100
    printsv(4, b); // 1, 11; 15, 101
  }

  a = input(0, 100, 2);
  printsv(0, a);
  b = a - 10;
  if (b * 4 == 48) {
    printsv(1, b); // 12, 12
    printsv(2, a); // 22, 22
  } else {
    printsv(3, b); // -10, 10; 14, 90
    printsv(4, a); // 0, 20; 24, 100
  }

  a = input(0, 100, 2);
  printsv(0, a);
  if (a - 10 == 48) {
    printsv(2, a);
  } else {
    printsv(4, a);
  }

  a = input(0, 100, 2);
  printsv(0, a);
  b = input(0, 100, 2);
  printsv(1, b);
  c = a + b;
  printsv(2, c);
  d = c + 1; // 1, 201
  printsv(2, d);
  if (d < 50) {   // unsupported
    printsv(3, a);
  } else {
    printsv(4, a);
  }

  a = input(0, 100, 2);
  printsv(0, a);
  b = input(0, 100, 2);
  printsv(1, b);
  c = a + b;
  printsv(2, c);
  d = c + 1; // 1, 201
  printsv(2, d);
  if (d < 202) {
    printsv(3, a); // 0, 100
  } else {
    printsv(4, a);
  }

  a = input(0, 100, 2);
  printsv(0, a);
  a = 1;
  b = input(0, 4294967295, 1);
  printsv(0, b);
  a = 2*b;
  printsv(1, a);

  a = input(0, -1, 1);
  printsv(0, a);
  b = 2 * a;
  printsv(1, b);
  b = a * 3;
  printsv(2, b);
  c = 1;
  c = c + b;
  printsv(3, c);
  c = c + b;
  printsv(4, c);

  a = input(1000, 100, 1);
  b = input(899, 10, 1);
  c = a + b;
  printsv(4, c);

  a = input(-4, -10, 1);
  c = a * -10;
  printsv(4, c);

  a = input(1, 0, 1);
  b = input(899, 10, 1);
  c = a * 2;
  printsv(4, c);

}