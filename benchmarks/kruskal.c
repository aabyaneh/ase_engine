uint64_t V = 10;
uint64_t* parent;

uint64_t find(uint64_t i) {
  while (*(parent + i) != i)
    i = *(parent + i);

  return i;
}

void union1(uint64_t i, uint64_t j) {
  uint64_t a;
  uint64_t b;

  a = find(i);
  b = find(j);

  *(parent + a) = b;
}

uint64_t kruskalMST(uint64_t* cost) {
  uint64_t mincost;
  uint64_t i;
  uint64_t edge_count;
  uint64_t min;
  uint64_t a;
  uint64_t b;
  uint64_t j;

  mincost = 0;

  i = 0;
  while (i < V) {
    *(parent + i) = i;

    i = i + 1;
  }

  edge_count = 0;
  while (edge_count < V - 1) {
    min = -1;
    a = -1;
    b = -1;

    i = 0;
    while (i < V) {
      j = 0;
      while (j < V) {
        if (find(i) != find(j)) {
          if (*((uint64_t*) *(cost + i) + j) < min) {
            min = *((uint64_t*) *(cost + i) + j);
            a = i;
            b = j;
          }
        }

        j = j + 1;
      }

      i = i + 1;
    }

    union1(a, b);
    mincost = mincost + min;
    edge_count = edge_count + 1;
  }

  return mincost;
}

uint64_t main() {
  uint64_t* graph;
  uint64_t i;
  uint64_t out;

  parent = malloc(8 * V);

  graph = malloc(8 * V);
  i = 0;
  while(i < V) {
    *(graph + i) = (uint64_t) malloc(8 * V);
    i = i + 1;
  }

  *((uint64_t*) *(graph + 0) + 0) = -1;
  *((uint64_t*) *(graph + 0) + 1) = 4;
  *((uint64_t*) *(graph + 0) + 2) = -1;
  *((uint64_t*) *(graph + 0) + 3) = -1;
  *((uint64_t*) *(graph + 0) + 4) = -1;
  *((uint64_t*) *(graph + 0) + 5) = -1;
  *((uint64_t*) *(graph + 0) + 6) = -1;
  *((uint64_t*) *(graph + 0) + 7) = 8;
  *((uint64_t*) *(graph + 0) + 8) = -1;

  *((uint64_t*) *(graph + 1) + 0) = 4;
  *((uint64_t*) *(graph + 1) + 1) = -1;
  *((uint64_t*) *(graph + 1) + 2) = 8;
  *((uint64_t*) *(graph + 1) + 3) = -1;
  *((uint64_t*) *(graph + 1) + 4) = -1;
  *((uint64_t*) *(graph + 1) + 5) = -1;
  *((uint64_t*) *(graph + 1) + 6) = -1;
  *((uint64_t*) *(graph + 1) + 7) = 11;
  *((uint64_t*) *(graph + 1) + 8) = -1;

  *((uint64_t*) *(graph + 2) + 0) = -1;
  *((uint64_t*) *(graph + 2) + 1) = 8;
  *((uint64_t*) *(graph + 2) + 2) = -1;
  *((uint64_t*) *(graph + 2) + 3) = 7;
  *((uint64_t*) *(graph + 2) + 4) = -1;
  *((uint64_t*) *(graph + 2) + 5) = 4;
  *((uint64_t*) *(graph + 2) + 6) = -1;
  *((uint64_t*) *(graph + 2) + 7) = -1;
  *((uint64_t*) *(graph + 2) + 8) = 2;

  *((uint64_t*) *(graph + 3) + 0) = -1;
  *((uint64_t*) *(graph + 3) + 1) = -1;
  *((uint64_t*) *(graph + 3) + 2) = 7;
  *((uint64_t*) *(graph + 3) + 3) = -1;
  *((uint64_t*) *(graph + 3) + 4) = 9;
  *((uint64_t*) *(graph + 3) + 5) = 14;
  *((uint64_t*) *(graph + 3) + 6) = -1;
  *((uint64_t*) *(graph + 3) + 7) = -1;
  *((uint64_t*) *(graph + 3) + 8) = -1;

  *((uint64_t*) *(graph + 4) + 0) = -1;
  *((uint64_t*) *(graph + 4) + 1) = -1;
  *((uint64_t*) *(graph + 4) + 2) = -1;
  *((uint64_t*) *(graph + 4) + 3) = 9;
  *((uint64_t*) *(graph + 4) + 4) = -1;
  *((uint64_t*) *(graph + 4) + 5) = 10;
  *((uint64_t*) *(graph + 4) + 6) = -1;
  *((uint64_t*) *(graph + 4) + 7) = -1;
  *((uint64_t*) *(graph + 4) + 8) = -1;

  *((uint64_t*) *(graph + 5) + 0) = -1;
  *((uint64_t*) *(graph + 5) + 1) = -1;
  *((uint64_t*) *(graph + 5) + 2) = 4;
  *((uint64_t*) *(graph + 5) + 3) = 14;
  *((uint64_t*) *(graph + 5) + 4) = 10;
  *((uint64_t*) *(graph + 5) + 5) = -1;
  *((uint64_t*) *(graph + 5) + 6) = 2;
  *((uint64_t*) *(graph + 5) + 7) = -1;
  *((uint64_t*) *(graph + 5) + 8) = -1;

  *((uint64_t*) *(graph + 6) + 0) = -1;
  *((uint64_t*) *(graph + 6) + 1) = -1;
  *((uint64_t*) *(graph + 6) + 2) = -1;
  *((uint64_t*) *(graph + 6) + 3) = -1;
  *((uint64_t*) *(graph + 6) + 4) = -1;
  *((uint64_t*) *(graph + 6) + 5) = 2;
  *((uint64_t*) *(graph + 6) + 6) = -1;
  *((uint64_t*) *(graph + 6) + 7) = 1;
  *((uint64_t*) *(graph + 6) + 8) = 6;

  *((uint64_t*) *(graph + 7) + 0) = 8;
  *((uint64_t*) *(graph + 7) + 1) = 11;
  *((uint64_t*) *(graph + 7) + 2) = -1;
  *((uint64_t*) *(graph + 7) + 3) = -1;
  *((uint64_t*) *(graph + 7) + 4) = -1;
  *((uint64_t*) *(graph + 7) + 5) = -1;
  *((uint64_t*) *(graph + 7) + 6) = 1;
  *((uint64_t*) *(graph + 7) + 7) = -1;
  *((uint64_t*) *(graph + 7) + 8) = 7;

  *((uint64_t*) *(graph + 8) + 0) = -1;
  *((uint64_t*) *(graph + 8) + 1) = -1;
  *((uint64_t*) *(graph + 8) + 2) = 2;
  *((uint64_t*) *(graph + 8) + 3) = -1;
  *((uint64_t*) *(graph + 8) + 4) = -1;
  *((uint64_t*) *(graph + 8) + 5) = -1;
  *((uint64_t*) *(graph + 8) + 6) = 6;
  *((uint64_t*) *(graph + 8) + 7) = 7;
  *((uint64_t*) *(graph + 8) + 8) = -1;

  // added node
  *((uint64_t*) *(graph + 0) + 9) = -1;
  *((uint64_t*) *(graph + 1) + 9) = -1;
  *((uint64_t*) *(graph + 2) + 9) = -1;
  *((uint64_t*) *(graph + 3) + 9) = 10;
  *((uint64_t*) *(graph + 4) + 9) = 10;
  *((uint64_t*) *(graph + 5) + 9) = -1;
  *((uint64_t*) *(graph + 6) + 9) = -1;
  *((uint64_t*) *(graph + 7) + 9) = -1;
  *((uint64_t*) *(graph + 8) + 9) = -1;
  //
  *((uint64_t*) *(graph + 9) + 0) = -1;
  *((uint64_t*) *(graph + 9) + 1) = -1;
  *((uint64_t*) *(graph + 9) + 2) = -1;
  *((uint64_t*) *(graph + 9) + 3) = 10;
  *((uint64_t*) *(graph + 9) + 4) = 10;
  *((uint64_t*) *(graph + 9) + 5) = -1;
  *((uint64_t*) *(graph + 9) + 6) = -1;
  *((uint64_t*) *(graph + 9) + 7) = -1;
  *((uint64_t*) *(graph + 9) + 8) = -1;
  *((uint64_t*) *(graph + 9) + 9) = -1;

  interval((uint64_t*) *(graph + 0) + 1, 1, 50, 1);
  interval((uint64_t*) *(graph + 1) + 0, 1, 50, 1);

  interval((uint64_t*) *(graph + 1) + 7, 1, 50, 1);
  interval((uint64_t*) *(graph + 7) + 1, 1, 50, 1);

  interval((uint64_t*) *(graph + 6) + 8, 1, 50, 1);
  interval((uint64_t*) *(graph + 8) + 6, 1, 50, 1);

  interval((uint64_t*) *(graph + 2) + 5, 1, 50, 1);
  interval((uint64_t*) *(graph + 5) + 2, 1, 50, 1);

  out = kruskalMST(graph);

  return 0;
}