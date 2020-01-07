uint64_t N = 100;

void multiply(uint64_t* mat1, uint64_t* mat2, uint64_t* matr) {
  uint64_t i;
  uint64_t j;
  uint64_t k;

  i = 0;
  while (i < N) {
    j = 0;
    while (j < N) {
      k = 0;
      while (k < N) {
        *(matr + (i * N + j)) = *(matr + (i * N + j)) + *(mat1 + (i * N + k)) * *(mat2 + (k * N + j));
        k = k + 1;
      }
      j = j + 1;
    }
    i = i + 1;
  }
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t i;
  uint64_t j;
  uint64_t* mat1;
  uint64_t* mat2;
  uint64_t* matr;
  uint64_t a;

  mat1 = malloc(N * N * 8);
  mat2 = malloc(N * N * 8);
  matr = malloc(N * N * 8);

  i = 0;
  while (i < N) {
    j = 0;
    while (j < N) {
      *(mat1 + (i * N + j)) = i + 1;
      *(mat2 + (i * N + j)) = i + 1;
      *(matr + (i * N + j)) = 0;
      j = j + 1;
    }
    i = i + 1;
  }

  i = 0;
  while (i < N) {
    input((mat1 + (i * N)), 0, 2*N, 1);
    i = i + 1;
  }

  // input((mat1 + (0 * N + 0)), 0, 2*N, 1);
  // input((mat1 + (1 * N + 0)), 0, 2*N, 1);
  // input((mat1 + (2 * N + 0)), 0, 2*N, 1);
  // input((mat1 + (3 * N + 0)), 0, 2*N, 1);
  // input((mat1 + (4 * N + 0)), 0, 2*N, 1);

  multiply(mat1, mat2, matr);

  i = 0;
  while (i < N) {
    j = 0;
    while (j < N) {
      if(*(matr + (i * N + j)) < 10*N) {
        // printsv((i * N + j), *(matr + (i * N + j)));
        a = *(matr + (i * N + j));
      }
      // else
        // printsv((i * N + j), *(matr + (i * N + j)));
      // printsv(j, *(matr + (i * N + j)));
      j = j + 1;
    }
    i = i + 1;
  }

  return 0;
}