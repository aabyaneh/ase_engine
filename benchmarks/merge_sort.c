uint64_t  read(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_read);
uint64_t  open(uint64_t* filename, uint64_t flags, uint64_t mode);
uint64_t* malloc(uint64_t size);

uint64_t* power_of_two_table;
uint64_t* character_buffer;
uint64_t  character;

void merge(uint64_t* arr, uint64_t l, uint64_t m, uint64_t r) {
  uint64_t i;
  uint64_t j;
  uint64_t k;
  uint64_t n1;
  uint64_t n2;
  uint64_t loop;
  uint64_t* L;
  uint64_t* R;

  n1 = m - l + 1;
  n2 = r - m;

  L = malloc(n1 * 8);
  R = malloc(n2 * 8);

  i = 0;
  while (i < n1) {
    *(L + i) = *(arr + (l+i));
    i = i + 1;
  }

  j = 0;
  while (j < n2) {
    *(R + j) = *(arr + (m+j+1));
    j = j + 1;
  }

  i = 0;
  j = 0;
  k = l;
  loop = 1;
  while (loop) {
    if (i < n1) {
      if (j < n2) {
        if (*(L + i) <= *(R + j)) {
          *(arr + k) = *(L + i);
          i = i + 1;
        } else {
          *(arr + k) = *(R + j);
          j = j + 1;
        }

        k = k + 1;
      } else {
        loop = 0;
      }
    } else {
      loop = 0;
    }
  }

  while (i < n1) {
    *(arr + k) = *(L + i);
    i = i + 1;
    k = k + 1;
  }

  while (j < n2) {
    *(arr + k) = *(R + j);
    j = j + 1;
    k = k + 1;
  }
}

void merge_sort(uint64_t* arr, uint64_t l, uint64_t r) {
  uint64_t m;

  if (l < r) {
    // (l+r)/2 without overflow
    m = l + (r-l)/2;

    merge_sort(arr, l, m);
    merge_sort(arr, m+1, r);

    merge(arr, l, m, r);
  }
}

void init() {
  uint64_t i;

  // powers of two table with CPUBITWIDTH entries for 2^0 to 2^(CPUBITWIDTH - 1)
  power_of_two_table = malloc(64 * 8);

  *power_of_two_table = 1; // 2^0 == 1

  i = 1;

  while (i < 64) {
    // compute powers of two incrementally using this recurrence relation
    *(power_of_two_table + i) = *(power_of_two_table + (i - 1)) * 2;

    i = i + 1;
  }

  character_buffer  = malloc(8);
  *character_buffer = 0;
}

uint64_t two_to_the_power_of(uint64_t p) {
  // assert: 0 <= p < CPUBITWIDTH
  return *(power_of_two_table + p);
}

uint64_t sign_extend(uint64_t n, uint64_t b) {
  // assert: 0 <= n <= 2^b
  // assert: 0 < b < CPUBITWIDTH
  if (n < two_to_the_power_of(b - 1))
    return n;
  else
    return n - two_to_the_power_of(b);
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t v1;
  uint64_t v2;
  uint64_t* source_name;
  uint64_t source_fd;
  uint64_t number_of_read_bytes;
  uint64_t cnt;
  uint64_t* arr;

  init();

  source_name = (uint64_t*) "in.c";

  source_fd = sign_extend(open(source_name, 32768, 0), 32);

  number_of_read_bytes = read(source_fd, character_buffer, 1);

  if (number_of_read_bytes == 1) {
    // store the read character in the global variable called character
    character = *character_buffer;
  } else if (number_of_read_bytes == 0) {
    character = -1;
  }

  cnt = 500;
  arr = malloc(cnt * 8);

  if (cnt < 2)
    return 0;

  v1 = 0;
  while (v1 < cnt - 1) {
    *(arr + v1) = cnt - v1;
    v1 = v1 + 1;
  }

  *(arr + cnt - 1) = character;

  merge_sort(arr, 0, cnt - 1);

  return 0;
}