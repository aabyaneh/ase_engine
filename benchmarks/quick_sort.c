uint64_t  read(uint64_t fd, uint64_t* buffer, uint64_t bytes_to_read);
uint64_t  open(uint64_t* filename, uint64_t flags, uint64_t mode);

uint64_t* power_of_two_table;
uint64_t* character_buffer;
uint64_t  character;
uint64_t  INT64_MIN_T;

uint64_t signed_less_than(uint64_t a, uint64_t b) {
  return a + INT64_MIN_T < b + INT64_MIN_T;
}

void swap(uint64_t* op1, uint64_t* op2) {
  uint64_t temp;

  temp = *op1;
  *op1 = *op2;
  *op2 = temp;
}

uint64_t partition(uint64_t* arr, uint64_t low, uint64_t high) {
  uint64_t pivot;
  uint64_t i;
  uint64_t j;

  pivot = *(arr + high);
  i     = low - 1;

  j = low;
  while (j < high) {
    if (*(arr + j) <= pivot) {
        i = i + 1;
        swap(arr + i, arr + j);
    }
    j = j + 1;
  }

  swap(arr + i + 1, arr + high);

  return i + 1;
}

void quick_sort(uint64_t* arr, uint64_t low, uint64_t high) {
  uint64_t pi;

  if (signed_less_than(low, high)) {
    pi = partition(arr, low, high);

    quick_sort(arr, low, pi - 1);
    quick_sort(arr, pi + 1, high);
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

  INT64_MIN_T = two_to_the_power_of(63);
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

  quick_sort(arr, 0, cnt - 1);

  return 0;
}