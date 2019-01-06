#include <sys/time.h>
#include <iostream>
#include <fstream>
#include <vector>
#include <queue>
#include <stack>
#include <map>
#include <string>
#include <algorithm>

struct timeval tv_begin;
struct timeval tv_end;

struct interval {
  int start, end, id;
  int predecessor_cnt;
  int value;
  std::vector<int>* lt_what_list;
};

std::map<int,int>*     var_id;
std::vector<interval>* elements;
std::vector<bool>*     is_element_valid;
unsigned int           valid_elements_cnt = 0;
unsigned int           scheduled_cnt = 0;

void less_than(interval l, interval r) {
  int lhs_idx;
  int rhs_idx;

  if (var_id->count(l.id) == 0) {
    elements->push_back(l);
    elements->back().lt_what_list = new std::vector<int>();
    is_element_valid->push_back(true);
    valid_elements_cnt++;
    lhs_idx = elements->size() - 1;
    var_id->insert(std::pair<int,int>(l.id, lhs_idx));
  } else {
    lhs_idx = var_id->find(l.id)->second;
    if (is_element_valid->at(lhs_idx) == false) {
      elements->at(lhs_idx).start = l.start;
      elements->at(lhs_idx).end   = l.end;
      elements->at(lhs_idx).value = l.value;
      is_element_valid->at(lhs_idx) = true;
      valid_elements_cnt++;
    }
  }

  if (var_id->count(r.id) == 0) {
    elements->push_back(r);
    elements->back().lt_what_list = new std::vector<int>();
    is_element_valid->push_back(true);
    valid_elements_cnt++;
    rhs_idx = elements->size() - 1;
    var_id->insert(std::pair<int,int>(r.id, rhs_idx));
  } else {
    rhs_idx = var_id->find(r.id)->second;
    if (is_element_valid->at(rhs_idx) == false) {
      elements->at(rhs_idx).start = r.start;
      elements->at(rhs_idx).end   = r.end;
      elements->at(rhs_idx).value = r.value;
      is_element_valid->at(rhs_idx) = true;
      valid_elements_cnt++;
    }
  }

  elements->at(lhs_idx).lt_what_list->push_back(rhs_idx);
  elements->at(rhs_idx).predecessor_cnt++;
}

void undo_less_than(interval lhs, interval rhs) {
  int lhs_idx = var_id->find(lhs.id)->second;
  int rhs_idx = var_id->find(rhs.id)->second;

  elements->at(lhs_idx).lt_what_list->pop_back();
  elements->at(rhs_idx).predecessor_cnt--;

  if (elements->at(lhs_idx).lt_what_list->size() == 0 && elements->at(lhs_idx).predecessor_cnt == 0) {
    is_element_valid->at(lhs_idx) = false;
    valid_elements_cnt--;
  }

  if (elements->at(rhs_idx).lt_what_list->size() == 0 && elements->at(rhs_idx).predecessor_cnt == 0) {
    is_element_valid->at(rhs_idx) = false;
    valid_elements_cnt--;
  }
}

bool path(interval path_start, std::vector<int>* query_predecessor_cnts) {
  int value;
  interval node;
  std::stack<interval,std::vector<interval> > stack;

  stack.push(path_start);

  while (stack.size()) {
    node = stack.top();
    stack.pop();

    value = node.value;

    if (node.start > value) {
      value = node.start;
      elements->at(var_id->find(node.id)->second).value = value;
    }
    if (node.end <= value)
      return false;

    value++;
    scheduled_cnt++;

    for (size_t i = 0; i < node.lt_what_list->size(); i++) {
      if (elements->at(node.lt_what_list->at(i)).value < value)
        elements->at(node.lt_what_list->at(i)).value = value;
      query_predecessor_cnts->at(node.lt_what_list->at(i))--;
      if (query_predecessor_cnts->at(node.lt_what_list->at(i)) == 0) {
        stack.push(elements->at(node.lt_what_list->at(i)));
      }
    }
  }

  return true;
}

bool explore_paths() {
  std::queue<int> qu;
  std::vector<int> query_predecessor_cnts(elements->size());

  scheduled_cnt = 0;

  for (size_t i = 0; i < elements->size(); i++) {
    query_predecessor_cnts.at(i) = elements->at(i).predecessor_cnt;

    if (is_element_valid->at(i) && elements->at(i).predecessor_cnt == 0) {
      qu.push(i);
    }
  }

  while (qu.size()) {
    if (!path(elements->at(qu.front()), &query_predecessor_cnts)) {
      return false;
    }
    qu.pop();
  }

  if (scheduled_cnt < valid_elements_cnt) {
    return false;
  }

  return true;
}

void init() {
  var_id   = new std::map<int,int>();
  elements = new std::vector<interval>();
  is_element_valid = new std::vector<bool>();
}

int main(int argc, char** argv) {
  interval in1;
  interval in2;
  interval in3;

  init();

  // [start, end)
  in1.start = 1;
  in1.end   = 3;
  in1.id    = 1;
  in1.value = 0;
  in1.predecessor_cnt = 0;

  in2.start = 1;
  in2.end   = 3;
  in2.id    = 2;
  in2.value = 0;
  in2.predecessor_cnt = 0;

  in3.start = 1;
  in3.end   = 3;
  in3.id    = 3;
  in3.value = 0;
  in3.predecessor_cnt = 0;

  less_than(in1, in2);
  less_than(in2, in3);

  std::cout << explore_paths() << '\n';

  undo_less_than(in2, in3);

  std::cout << explore_paths() << '\n';

  return 0;
}