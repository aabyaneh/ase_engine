/*
  Count pairs with average present in the same array
*/

uint64_t number_of_students=60;
uint64_t course_cnt=60;
uint64_t course_units_sum;
uint64_t number_of_students_passed;

uint64_t avg_arr(uint64_t* stud, uint64_t* crs_unit) {
  uint64_t i;
  uint64_t j;
  uint64_t* avgs;

  avgs = malloc(number_of_students * 8);

  i = 0;
  while (i < number_of_students) {
    j = 0;
    while (j < course_cnt) {
      *(avgs + i) = *(avgs + i) + *(stud + (i * course_cnt + j)) * *(crs_unit + j);
      j = j + 1;
    }
    i = i + 1;
  }

  i = 0;
  number_of_students_passed = 0;
  while (i < number_of_students) {
    if (*(avgs + i) / course_units_sum < 3) {
      number_of_students_passed = number_of_students_passed + 1;
    }
    i = i + 1;
  }

  // printsv(1, number_of_students_passed);

  return number_of_students_passed;
}

uint64_t main(uint64_t argc, uint64_t* argv) {
  uint64_t i;
  uint64_t j;
  uint64_t cnt;
  uint64_t* course_units;
  uint64_t* students;

  // number_of_students = 100;
  // course_cnt         = 100;
  // printsv(1, number_of_students);
  // printsv(2, course_cnt);
  course_units = malloc(course_cnt * 8);
  students     = malloc(number_of_students * course_cnt * 8);

  i = 0;
  course_units_sum = 0;
  while (i < course_cnt) {
    if (i % 2)
      *(course_units + i) = 4;
    else
      *(course_units + i) = 2;

    course_units_sum = course_units_sum + *(course_units + i);

    i = i + 1;
  }

  i = 0;
  cnt = 0;
  while (i < number_of_students) {
    j = 0;
    while (j < course_cnt) {
      if (cnt % 5 == 0)
        *(students + (i * course_cnt + j)) = 1;
      else if (cnt % 5 == 1)
        *(students + (i * course_cnt + j)) = 2;
      else if (cnt % 5 == 2)
        *(students + (i * course_cnt + j)) = 3;
      else if (cnt % 5 == 3)
        *(students + (i * course_cnt + j)) = 4;
      else
        *(students + (i * course_cnt + j)) = 5;

      j = j + 1;
    }
    cnt = cnt + 1;
    i = i + 1;
  }

  i = 0;
  while (i < number_of_students) {
    input((students + (i * course_cnt + (course_cnt/2))), 1, 5, 1);
    i = i + 1;
  }

  avg_arr(students, course_units);

  return 0;
}