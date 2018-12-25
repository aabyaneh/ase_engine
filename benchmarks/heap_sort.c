uint64_t  read(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_read);
uint64_t  open(uint64_t* filename, uint64_t flags, uint64_t mode);

uint64_t* power_of_two_table;
uint64_t* character_buffer;
uint64_t  character;

void swap(uint64_t* op1, uint64_t* op2) {
  uint64_t temp;

  temp = *op1;
  *op1 = *op2;
  *op2 = temp;
}

void heapify(uint64_t* arr, uint64_t n, uint64_t i) {
  uint64_t largest;
  uint64_t l;
  uint64_t r;

  largest = i;
  l = 2 * i + 1;
  r = 2 * i + 2;

  if (l < n)
    if (*(arr + l) > *(arr + largest))
      largest = l;

  if (r < n)
    if (*(arr + r) > *(arr + largest))
      largest = r;

  if (largest != i) {
    swap((arr + i), (arr + largest));
    heapify(arr, n, largest);
  }
}

void heap_sort(uint64_t* arr, uint64_t n) {
  uint64_t i;

  i = n / 2;
  while (i > 0) {
    heapify(arr, n, i - 1);

    i = i - 1;
  }

  i = n;
  while (i > 0) {
    swap(arr, (arr + (i-1)));
    heapify(arr, i-1, 0);

    i = i - 1;
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

  v1 = 0;
  while (v1 < cnt - 1) {
    *(arr + v1) = cnt - v1;
    v1 = v1 + 1;
  }

  *(arr + cnt - 1) = character;

  heap_sort(arr, cnt);

  return 0;
}