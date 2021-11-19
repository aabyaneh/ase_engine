uint64_t INT_MAX;
uint64_t INT64_MIN_T;

uint64_t signed_less_than(uint64_t a, uint64_t b) {
  return a + INT64_MIN_T < b + INT64_MIN_T;
}

void BellmanFord(uint64_t* graph, uint64_t V, uint64_t E, uint64_t src) {
  uint64_t* dis;
  uint64_t i;
  uint64_t j;

  dis = malloc(8 * V);

  i = 0;
  while (i < V) {
    *(dis + i) = INT_MAX;
    i = i + 1;
  }

  *(dis + src) = 0;

  i = 0;
  while (i < V - 1) {
    j = 0;
    while (j < E) {
      if ( signed_less_than( *(dis + *((uint64_t*) *(graph + j) + 0)) + *((uint64_t*) *(graph + j) + 2), *(dis + *((uint64_t*) *(graph + j) + 1)) ) != 0  ) {
        *(dis + *((uint64_t*) *(graph + j) + 1)) = *(dis + *((uint64_t*) *(graph + j) + 0)) + *((uint64_t*) *(graph + j) + 2);
      }

      j = j + 1;
    }

    i = i + 1;
  }
}

uint64_t main() {
  uint64_t* graph;
  uint64_t i;
  uint64_t out;
  uint64_t V;
  uint64_t E;

  INT_MAX = 9223372036854775807;
  INT64_MIN_T = 9223372036854775808;

  V = 10;
  E = 32;

  graph = malloc(8 * E);
  i = 0;
  while(i < E) {
    *(graph + i) = (uint64_t) malloc(8 * 3);
    i = i + 1;
  }

  *((uint64_t*) *(graph + 0) + 0) = 0;
  *((uint64_t*) *(graph + 0) + 1) = 1;
  *((uint64_t*) *(graph + 0) + 2) = 4;

  *((uint64_t*) *(graph + 1) + 0) = 1;
  *((uint64_t*) *(graph + 1) + 1) = 0;
  *((uint64_t*) *(graph + 1) + 2) = 4;

  *((uint64_t*) *(graph + 2) + 0) = 0;
  *((uint64_t*) *(graph + 2) + 1) = 7;
  *((uint64_t*) *(graph + 2) + 2) = 8;

  *((uint64_t*) *(graph + 3) + 0) = 7;
  *((uint64_t*) *(graph + 3) + 1) = 0;
  *((uint64_t*) *(graph + 3) + 2) = 8;

  *((uint64_t*) *(graph + 4) + 0) = 1;
  *((uint64_t*) *(graph + 4) + 1) = 2;
  *((uint64_t*) *(graph + 4) + 2) = 8;

  *((uint64_t*) *(graph + 5) + 0) = 2;
  *((uint64_t*) *(graph + 5) + 1) = 1;
  *((uint64_t*) *(graph + 5) + 2) = 8;

  *((uint64_t*) *(graph + 6) + 0) = 1;
  *((uint64_t*) *(graph + 6) + 1) = 7;
  *((uint64_t*) *(graph + 6) + 2) = 11;

  *((uint64_t*) *(graph + 7) + 0) = 7;
  *((uint64_t*) *(graph + 7) + 1) = 1;
  *((uint64_t*) *(graph + 7) + 2) = 11;

  *((uint64_t*) *(graph + 8) + 0) = 7;
  *((uint64_t*) *(graph + 8) + 1) = 8;
  *((uint64_t*) *(graph + 8) + 2) = 7;

  *((uint64_t*) *(graph + 9) + 0) = 8;
  *((uint64_t*) *(graph + 9) + 1) = 7;
  *((uint64_t*) *(graph + 9) + 2) = 7;

  *((uint64_t*) *(graph + 10) + 0) = 7;
  *((uint64_t*) *(graph + 10) + 1) = 6;
  *((uint64_t*) *(graph + 10) + 2) = 1;

  *((uint64_t*) *(graph + 11) + 0) = 6;
  *((uint64_t*) *(graph + 11) + 1) = 7;
  *((uint64_t*) *(graph + 11) + 2) = 1;

  *((uint64_t*) *(graph + 12) + 0) = 2;
  *((uint64_t*) *(graph + 12) + 1) = 3;
  *((uint64_t*) *(graph + 12) + 2) = 7;

  *((uint64_t*) *(graph + 13) + 0) = 3;
  *((uint64_t*) *(graph + 13) + 1) = 2;
  *((uint64_t*) *(graph + 13) + 2) = 7;

  *((uint64_t*) *(graph + 14) + 0) = 2;
  *((uint64_t*) *(graph + 14) + 1) = 5;
  *((uint64_t*) *(graph + 14) + 2) = 4;

  *((uint64_t*) *(graph + 15) + 0) = 5;
  *((uint64_t*) *(graph + 15) + 1) = 2;
  *((uint64_t*) *(graph + 15) + 2) = 4;

  *((uint64_t*) *(graph + 16) + 0) = 2;
  *((uint64_t*) *(graph + 16) + 1) = 8;
  *((uint64_t*) *(graph + 16) + 2) = 2;

  *((uint64_t*) *(graph + 17) + 0) = 8;
  *((uint64_t*) *(graph + 17) + 1) = 2;
  *((uint64_t*) *(graph + 17) + 2) = 2;

  *((uint64_t*) *(graph + 18) + 0) = 6;
  *((uint64_t*) *(graph + 18) + 1) = 8;
  *((uint64_t*) *(graph + 18) + 2) = 6;

  *((uint64_t*) *(graph + 19) + 0) = 8;
  *((uint64_t*) *(graph + 19) + 1) = 6;
  *((uint64_t*) *(graph + 19) + 2) = 6;

  *((uint64_t*) *(graph + 20) + 0) = 6;
  *((uint64_t*) *(graph + 20) + 1) = 5;
  *((uint64_t*) *(graph + 20) + 2) = 2;

  *((uint64_t*) *(graph + 21) + 0) = 5;
  *((uint64_t*) *(graph + 21) + 1) = 6;
  *((uint64_t*) *(graph + 21) + 2) = 2;

  *((uint64_t*) *(graph + 22) + 0) = 3;
  *((uint64_t*) *(graph + 22) + 1) = 4;
  *((uint64_t*) *(graph + 22) + 2) = 9;

  *((uint64_t*) *(graph + 23) + 0) = 4;
  *((uint64_t*) *(graph + 23) + 1) = 3;
  *((uint64_t*) *(graph + 23) + 2) = 9;

  *((uint64_t*) *(graph + 24) + 0) = 3;
  *((uint64_t*) *(graph + 24) + 1) = 5;
  *((uint64_t*) *(graph + 24) + 2) = 14;

  *((uint64_t*) *(graph + 25) + 0) = 5;
  *((uint64_t*) *(graph + 25) + 1) = 3;
  *((uint64_t*) *(graph + 25) + 2) = 14;

  *((uint64_t*) *(graph + 26) + 0) = 5;
  *((uint64_t*) *(graph + 26) + 1) = 4;
  *((uint64_t*) *(graph + 26) + 2) = 10;

  *((uint64_t*) *(graph + 27) + 0) = 4;
  *((uint64_t*) *(graph + 27) + 1) = 5;
  *((uint64_t*) *(graph + 27) + 2) = 10;

  // added
  *((uint64_t*) *(graph + 28) + 0) = 3;
  *((uint64_t*) *(graph + 28) + 1) = 9;
  *((uint64_t*) *(graph + 28) + 2) = 10;

  *((uint64_t*) *(graph + 29) + 0) = 9;
  *((uint64_t*) *(graph + 29) + 1) = 3;
  *((uint64_t*) *(graph + 29) + 2) = 10;

  *((uint64_t*) *(graph + 30) + 0) = 4;
  *((uint64_t*) *(graph + 30) + 1) = 9;
  *((uint64_t*) *(graph + 30) + 2) = 10;

  *((uint64_t*) *(graph + 31) + 0) = 9;
  *((uint64_t*) *(graph + 31) + 1) = 4;
  *((uint64_t*) *(graph + 31) + 2) = 10;

  interval((uint64_t*) *(graph + 0) + 2, 1, 50, 1);
  interval((uint64_t*) *(graph + 1) + 2, 1, 50, 1);

  interval((uint64_t*) *(graph + 4) + 2, 1, 50, 1);
  interval((uint64_t*) *(graph + 5) + 2, 1, 50, 1);

  interval((uint64_t*) *(graph + 14) + 2, 1, 50, 1);
  interval((uint64_t*) *(graph + 15) + 2, 1, 50, 1);

  interval((uint64_t*) *(graph + 26) + 2, 1, 50, 1);
  interval((uint64_t*) *(graph + 27) + 2, 1, 50, 1);

  interval((uint64_t*) *(graph + 30) + 2, 1, 50, 1);
  interval((uint64_t*) *(graph + 31) + 2, 1, 50, 1);

  BellmanFord(graph, V, E, 0);

  return 0;
}