uint64_t V = 10;

uint64_t minDistance(uint64_t* dist, uint64_t* sptSet) {
  uint64_t min;
  uint64_t min_index;
  uint64_t v;

  min = -1;

  v = 0;
  while (v < V) {
    if (*(sptSet + v) == 0) {
      if (*(dist + v) <= min) {
        min = *(dist + v);
        min_index = v;
      }
    }

    v = v + 1;
  }

  return min_index;
}

void dijkstra(uint64_t* graph, uint64_t src) {
  uint64_t* dist;
  uint64_t* sptSet;
  uint64_t i;
  uint64_t count;
  uint64_t u;
  uint64_t v;

  dist = malloc(8 * V);
  sptSet = malloc(8 * V);

  i = 0;
  while(i < V) {
    *(dist + i) = -1;
    *(sptSet + i) = 0;

    i = i + 1;
  }

  *(dist + src) = 0;

  count = 0;
  while (count < V - 1) {
    u = minDistance(dist, sptSet);

    *(sptSet + u) = 1;

    v = 0;
    while (v < V) {
      if (*(sptSet + v) == 0) {
        if ( *((uint64_t*) *(graph + u) + v) > 0 ) {
          if ( *(dist + u) < -1) {
            if ( *(dist + u) +  *((uint64_t*) *(graph + u) + v) < *(dist + v) ) {
              *(dist + v) = *(dist + u) + *((uint64_t*) *(graph + u) + v);
            }
          }
        }
      }

      v = v + 1;
    }

    count = count + 1;
  }
}

uint64_t main() {
  uint64_t* graph;
  uint64_t i;
  uint64_t out;

  graph = malloc(8 * V);
  i = 0;
  while(i < V) {
    *(graph + i) = (uint64_t) malloc(8 * V);
    i = i + 1;
  }

  *((uint64_t*) *(graph + 0) + 0) = 0;
  *((uint64_t*) *(graph + 0) + 1) = 4;
  *((uint64_t*) *(graph + 0) + 2) = 0;
  *((uint64_t*) *(graph + 0) + 3) = 0;
  *((uint64_t*) *(graph + 0) + 4) = 0;
  *((uint64_t*) *(graph + 0) + 5) = 0;
  *((uint64_t*) *(graph + 0) + 6) = 0;
  *((uint64_t*) *(graph + 0) + 7) = 8;
  *((uint64_t*) *(graph + 0) + 8) = 0;

  *((uint64_t*) *(graph + 1) + 0) = 4;
  *((uint64_t*) *(graph + 1) + 1) = 0;
  *((uint64_t*) *(graph + 1) + 2) = 8;
  *((uint64_t*) *(graph + 1) + 3) = 0;
  *((uint64_t*) *(graph + 1) + 4) = 0;
  *((uint64_t*) *(graph + 1) + 5) = 0;
  *((uint64_t*) *(graph + 1) + 6) = 0;
  *((uint64_t*) *(graph + 1) + 7) = 11;
  *((uint64_t*) *(graph + 1) + 8) = 0;

  *((uint64_t*) *(graph + 2) + 0) = 0;
  *((uint64_t*) *(graph + 2) + 1) = 8;
  *((uint64_t*) *(graph + 2) + 2) = 0;
  *((uint64_t*) *(graph + 2) + 3) = 7;
  *((uint64_t*) *(graph + 2) + 4) = 0;
  *((uint64_t*) *(graph + 2) + 5) = 4;
  *((uint64_t*) *(graph + 2) + 6) = 0;
  *((uint64_t*) *(graph + 2) + 7) = 0;
  *((uint64_t*) *(graph + 2) + 8) = 2;

  *((uint64_t*) *(graph + 3) + 0) = 0;
  *((uint64_t*) *(graph + 3) + 1) = 0;
  *((uint64_t*) *(graph + 3) + 2) = 7;
  *((uint64_t*) *(graph + 3) + 3) = 0;
  *((uint64_t*) *(graph + 3) + 4) = 9;
  *((uint64_t*) *(graph + 3) + 5) = 14;
  *((uint64_t*) *(graph + 3) + 6) = 0;
  *((uint64_t*) *(graph + 3) + 7) = 0;
  *((uint64_t*) *(graph + 3) + 8) = 0;

  *((uint64_t*) *(graph + 4) + 0) = 0;
  *((uint64_t*) *(graph + 4) + 1) = 0;
  *((uint64_t*) *(graph + 4) + 2) = 0;
  *((uint64_t*) *(graph + 4) + 3) = 9;
  *((uint64_t*) *(graph + 4) + 4) = 0;
  *((uint64_t*) *(graph + 4) + 5) = 10;
  *((uint64_t*) *(graph + 4) + 6) = 0;
  *((uint64_t*) *(graph + 4) + 7) = 0;
  *((uint64_t*) *(graph + 4) + 8) = 0;

  *((uint64_t*) *(graph + 5) + 0) = 0;
  *((uint64_t*) *(graph + 5) + 1) = 0;
  *((uint64_t*) *(graph + 5) + 2) = 4;
  *((uint64_t*) *(graph + 5) + 3) = 14;
  *((uint64_t*) *(graph + 5) + 4) = 10;
  *((uint64_t*) *(graph + 5) + 5) = 0;
  *((uint64_t*) *(graph + 5) + 6) = 2;
  *((uint64_t*) *(graph + 5) + 7) = 0;
  *((uint64_t*) *(graph + 5) + 8) = 0;

  *((uint64_t*) *(graph + 6) + 0) = 0;
  *((uint64_t*) *(graph + 6) + 1) = 0;
  *((uint64_t*) *(graph + 6) + 2) = 0;
  *((uint64_t*) *(graph + 6) + 3) = 0;
  *((uint64_t*) *(graph + 6) + 4) = 0;
  *((uint64_t*) *(graph + 6) + 5) = 2;
  *((uint64_t*) *(graph + 6) + 6) = 0;
  *((uint64_t*) *(graph + 6) + 7) = 1;
  *((uint64_t*) *(graph + 6) + 8) = 6;

  *((uint64_t*) *(graph + 7) + 0) = 8;
  *((uint64_t*) *(graph + 7) + 1) = 11;
  *((uint64_t*) *(graph + 7) + 2) = 0;
  *((uint64_t*) *(graph + 7) + 3) = 0;
  *((uint64_t*) *(graph + 7) + 4) = 0;
  *((uint64_t*) *(graph + 7) + 5) = 0;
  *((uint64_t*) *(graph + 7) + 6) = 1;
  *((uint64_t*) *(graph + 7) + 7) = 0;
  *((uint64_t*) *(graph + 7) + 8) = 7;

  *((uint64_t*) *(graph + 8) + 0) = 0;
  *((uint64_t*) *(graph + 8) + 1) = 0;
  *((uint64_t*) *(graph + 8) + 2) = 2;
  *((uint64_t*) *(graph + 8) + 3) = 0;
  *((uint64_t*) *(graph + 8) + 4) = 0;
  *((uint64_t*) *(graph + 8) + 5) = 0;
  *((uint64_t*) *(graph + 8) + 6) = 6;
  *((uint64_t*) *(graph + 8) + 7) = 7;
  *((uint64_t*) *(graph + 8) + 8) = 0;

  // added node
  *((uint64_t*) *(graph + 0) + 9) = 0;
  *((uint64_t*) *(graph + 1) + 9) = 0;
  *((uint64_t*) *(graph + 2) + 9) = 0;
  *((uint64_t*) *(graph + 3) + 9) = 10;
  *((uint64_t*) *(graph + 4) + 9) = 10;
  *((uint64_t*) *(graph + 5) + 9) = 0;
  *((uint64_t*) *(graph + 6) + 9) = 0;
  *((uint64_t*) *(graph + 7) + 9) = 0;
  *((uint64_t*) *(graph + 8) + 9) = 0;
  //
  *((uint64_t*) *(graph + 9) + 0) = 0;
  *((uint64_t*) *(graph + 9) + 1) = 0;
  *((uint64_t*) *(graph + 9) + 2) = 0;
  *((uint64_t*) *(graph + 9) + 3) = 10;
  *((uint64_t*) *(graph + 9) + 4) = 10;
  *((uint64_t*) *(graph + 9) + 5) = 0;
  *((uint64_t*) *(graph + 9) + 6) = 0;
  *((uint64_t*) *(graph + 9) + 7) = 0;
  *((uint64_t*) *(graph + 9) + 8) = 0;
  *((uint64_t*) *(graph + 9) + 9) = 0;

  interval((uint64_t*) *(graph + 0) + 1, 1, 50, 1);
  interval((uint64_t*) *(graph + 1) + 0, 1, 50, 1);

  interval((uint64_t*) *(graph + 1) + 7, 1, 50, 1);
  interval((uint64_t*) *(graph + 7) + 1, 1, 50, 1);

  interval((uint64_t*) *(graph + 6) + 8, 1, 50, 1);
  interval((uint64_t*) *(graph + 8) + 6, 1, 50, 1);

  interval((uint64_t*) *(graph + 2) + 5, 1, 50, 1);
  interval((uint64_t*) *(graph + 5) + 2, 1, 50, 1);

  interval((uint64_t*) *(graph + 3) + 4, 1, 50, 1);
  interval((uint64_t*) *(graph + 4) + 3, 1, 50, 1);

  interval((uint64_t*) *(graph + 7) + 8, 1, 50, 1);
  interval((uint64_t*) *(graph + 8) + 7, 1, 50, 1);

  interval((uint64_t*) *(graph + 4) + 9, 1, 50, 1);
  interval((uint64_t*) *(graph + 9) + 4, 1, 50, 1);

  dijkstra(graph, 0);

  return 0;
}