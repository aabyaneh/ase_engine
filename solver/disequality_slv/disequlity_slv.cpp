#include <sys/time.h>
#include <iostream>
#include <fstream>
#include <vector>
#include <map>
#include <string>
#include <algorithm>
#include "z3++.h"

using namespace z3;

struct timeval tv_begin;
struct timeval tv_end;

// ---------------------------------
// implementation of disjoint sets
// ---------------------------------

struct interval {
  int start, end, id;
};

bool compare_interval_start(interval i1, interval i2) {
  return (i1.start < i2.start);
}

bool compare_interval_end(interval i1, interval i2) {
  return (i1.end < i2.end);
}

struct sets_elements {
  std::vector<interval>* elements;
  std::vector<int>*      sets_linkedlist;
};

class disjoint_set {
  public:
    sets_elements* sets;
    std::vector<interval>* disjoint_sets;
    std::map<int,int>* var_id;
    int ds_num;

    void init_disjoint_sets();
    void add_element(interval);
    int  find(int);
    void union_sets(int, int);
    void create_disjoint_sets();
    void destroy_disjoint_sets();
};

void disjoint_set::init_disjoint_sets() {
  sets                  = new sets_elements();
  sets->elements        = new std::vector<interval>();
  sets->sets_linkedlist = new std::vector<int>();
  var_id                = new std::map<int,int>();
}

void disjoint_set::add_element(interval elem) {
  if (var_id->count(elem.id) == 0) {
    sets->elements->push_back(elem);
    sets->sets_linkedlist->push_back(-2);
    var_id->insert(std::pair<int,int>(elem.id, sets->elements->size() - 1));
  }
}

int disjoint_set::find(int i) {
  if (sets->sets_linkedlist->at(i) == -2) {
    sets->sets_linkedlist->at(i) = -1;
    return i;
  } else if (sets->sets_linkedlist->at(i) == -1) {
    return i;
  }

  return find(sets->sets_linkedlist->at(i));
}

void disjoint_set::union_sets(int i, int j) {
  int s1 = find(var_id->find(i)->second);
  int s2 = find(var_id->find(j)->second);
  if (s1 != s2) {
    if (s1 < s2)
      sets->sets_linkedlist->at(s1) = s2;
    else
      sets->sets_linkedlist->at(s2) = s1;
  }
}

void disjoint_set::create_disjoint_sets() {
  int j;
  int prev_j;
  int cnt;
  ds_num = 0;

  cnt = sets->elements->size();

  std::vector<std::vector<interval> >* dsets = new std::vector<std::vector<interval> > [cnt];

  for (size_t i = 0; i < cnt; i++) {
    if (sets->sets_linkedlist->at(i) >= 0) {
      j = i;
      std::vector<interval> s;
      while (sets->sets_linkedlist->at(j) >= 0) {
        s.push_back(sets->elements->at(j));
        prev_j = j;
        j = sets->sets_linkedlist->at(j);
        sets->sets_linkedlist->at(prev_j) = -2;
      }

      if (sets->sets_linkedlist->at(j) == -1) {
        if (dsets[j].size() == 0)
          ds_num++;
        dsets[j].push_back(s);
      } else
        std::cout << " error: " << sets->sets_linkedlist->at(j) << '\n';
    }
  }

  disjoint_sets = new std::vector<interval> [ds_num];
  int idx = 0;
  for (size_t i = 0; i < cnt; i++) {
    std::vector<interval> v;
    if (dsets[i].size()) {
      for (size_t j = 0; j < dsets[i].size(); j++) {
        v.insert(v.end(), dsets[i][j].begin(), dsets[i][j].end());
        dsets[i][j].clear();
      }
      v.push_back(sets->elements->at(i));
      dsets[i].clear();
      disjoint_sets[idx++] = v;
    }
  }

  delete[] dsets;
}

void disjoint_set::destroy_disjoint_sets() {
  for (size_t i = 0; i < ds_num; i++) {
    disjoint_sets[i].clear();
  }

  delete sets;
  delete sets->elements;
  delete sets->sets_linkedlist;
  delete var_id;
  delete[] disjoint_sets;
}

// ---------------------------------
// main function
// ---------------------------------

int main(int argc, char** argv) {
  std::vector<std::string> strings;
  std::vector<std::vector<int> > ids;
  unsigned int fuzz = atoi(argv[1]);
  unsigned int cnt = 0;

  // ---------------------------------
  // input chars
  // ---------------------------------

  std::string input = argv[2];
  std::ifstream inputs;
  inputs.open(input);

  char ch;
  std::string str;
  std::vector<int> id;
  while(inputs.get(ch)) {
    if ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9' && str.size()) || (ch == '_' && str.size()) ) {
      str.push_back(ch);
      id.push_back(cnt++);
    } else if (str.size()) {
      strings.push_back(str);
      ids.push_back(id);
      str.clear();
      id.clear();
    } else {
      std::cout << "error \n";
    }
  }
  if (str.size()) {
    strings.push_back(str);
    ids.push_back(id);
    str.clear();
    id.clear();
  }

  // ---------------------------------
  // edf scheduling algorithm
  // without using smt solver
  // ---------------------------------

  std::cout << "=========================" << '\n';
  gettimeofday(&tv_begin,NULL);

  disjoint_set ds;
  ds.init_disjoint_sets();

  interval in1;
  interval in2;
  for (unsigned int i = 0; i < strings.size(); i++) {
    for (unsigned int k = 0; k < i; k++) {
      if (strings.at(i).size() == strings.at(k).size()) {
        for (unsigned int l = 0; l < strings.at(i).size(); l++) {
          in1.start = (int)strings.at(i).at(l) - fuzz;
          in1.end   = (int)strings.at(i).at(l) + fuzz - 1;
          in1.id    = (int)ids.at(i).at(l);
          in2.start = (int)strings.at(k).at(l) - fuzz;
          in2.end   = (int)strings.at(k).at(l) + fuzz - 1;
          in2.id    = (int)ids.at(k).at(l);
          ds.add_element(in1);
          ds.add_element(in2);
          ds.union_sets(in1.id, in2.id);
        }
      }
    }
  }

  ds.create_disjoint_sets();
  std::cout << "number of disjoint sets: " << ds.ds_num << '\n';
  std::cout << "query_1 edf: " << '\n';

  // scheduling algorithm
  bool is_query_sat = true;
  for (size_t i = 0; i < ds.ds_num; i++) {
    std::vector<interval> disequal_ranges = ds.disjoint_sets[i];

    std::sort(disequal_ranges.begin(), disequal_ranges.end(), compare_interval_start);
    unsigned int time = disequal_ranges[0].start;
    unsigned int lo_cnt = 0;
    unsigned int up_cnt = 0;
    bool is_sat = true;

    while (lo_cnt < disequal_ranges.size()) {
      if (lo_cnt == up_cnt)
        time = disequal_ranges[up_cnt].start;

      while (up_cnt < disequal_ranges.size() && disequal_ranges[up_cnt].start == time) {
        up_cnt++;
        // std::cout << up_cnt << '\n';
      }

      std::sort(disequal_ranges.begin() + lo_cnt, disequal_ranges.begin() + up_cnt - 1, compare_interval_end);
      if (time < disequal_ranges[lo_cnt].end) {
        time++;
        lo_cnt++;
        // std::cout << time << " " << disequal_ranges[up_cnt].start << " " << lo_cnt << " " << up_cnt << " " << disequal_ranges.size() << '\n';
      } else {
        is_sat = false;
        // std::cout << time << " " << disequal_ranges[lo_cnt].start << " " << disequal_ranges[lo_cnt].end << '\n';
        break;
      }
    }

    if (is_sat) {
      std::cout << "sat" << '\n';
    } else {
      is_query_sat = false;
      std::cout << "unsat" << '\n';
      //break;
    }
  }

  gettimeofday(&tv_end,NULL);
  if (is_query_sat)
    std::cout << "totally sat" << '\n';
  else
    std::cout << "totally unsat" << '\n';

  double time_elapsed_in_mcseconds = (tv_end.tv_sec - tv_begin.tv_sec) * 1000000 + (tv_end.tv_usec- tv_begin.tv_usec);
  std::cout << "time edf: " << time_elapsed_in_mcseconds/1000000 << '\n';

  // ---------------------------------
  // using z3 smt solver
  // ---------------------------------

  std::cout << "=========================" << '\n';
  context c;
  solver s(c);
  cnt = 0;
  std::vector<std::vector<expr> > strings_bv;
  for (unsigned int i = 0; i < strings.size(); i++) {
    std::vector<expr> x;
    for (unsigned int j = 0; j < strings.at(i).size(); j++) {
      std::stringstream x_name;
      x_name << "x_" << cnt++;
      x.push_back(c.bv_const(x_name.str().c_str(), 8));
      s.add(ugt(x.back(), (unsigned int)strings.at(i).at(j) - fuzz));
      s.add(ult(x.back(), (unsigned int)strings.at(i).at(j) + fuzz));
    }
    strings_bv.push_back(x);
  }

  std::cout << "number of init constraints: " << cnt*2 << '\n';
  cnt = 0;
  // s.push();
  for (unsigned int i = 0; i < strings.size(); i++) {
    for (unsigned int k = 0; k < i; k++) {
      if (strings.at(i).size() == strings.at(k).size()) {
        for (unsigned int l = 0; l < strings.at(i).size(); l++) {
          s.add(strings_bv[k][l] != strings_bv[i][l]);
          cnt++;
          // if (cnt % 10 == 0) {
          //   std::cout << cnt << " " << s.check() << "\n";
          //   s.push();
          // }
        }
      }
    }
  }

  std::cout << "number of disequality constraints: " << cnt << '\n';

  std::cout << "query_2 z3 smt: " << '\n';
  gettimeofday(&tv_begin,NULL);
  std::cout << s.check() << "\n";
  gettimeofday(&tv_end,NULL);
  time_elapsed_in_mcseconds = (tv_end.tv_sec - tv_begin.tv_sec) * 1000000 + (tv_end.tv_usec- tv_begin.tv_usec);
  std::cout << "time z3: " << time_elapsed_in_mcseconds/1000000 << '\n';

  return 0;
}
