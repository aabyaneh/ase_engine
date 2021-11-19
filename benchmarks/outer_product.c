uint64_t M = 6;
uint64_t N = 6;

uint64_t main() {
  uint64_t i;
  uint64_t j;
  uint64_t* vec1;
  uint64_t* vec2;
  uint64_t* matr;
  uint64_t a;

  vec1 = malloc(M * 8);
  vec2 = malloc(N * 8);
  matr = malloc(M * N * 8);

  i = 0;
  while (i < M) {
    interval((vec1 + i), 0, 2*M, 1);
    i = i + 1;
  }

  i = 0;
  while (i < N) {
    *(vec2 + i) = i + 1;
    i = i + 1;
  }

  i = 0;
  while (i < M) {
    j = 0;
    while (j < N) {
      *(matr + (i * N + j)) = *(vec1 + i) * *(vec2 + j);
      j = j + 1;
    }
    i = i + 1;
  }

  i = 0;
  while (i < M) {
    j = 0;
    while (j < N) {
      if(*(matr + (i * N + j)) < N) {
        a = *(matr + (i * N + j));
      }
      j = j + 1;
    }
    i = i + 1;
  }

  return 0;
}