#include <sys/time.h>
#include <iostream>
#include <fstream>
#include <vector>
#include <queue>
#include <map>
#include <string>
#include <algorithm>

struct timeval tv_begin;
struct timeval tv_end;

struct interval {
  int start, end, id;
  int predecessor_cnt;
  std::vector<int>* lt_what_list;
};

std::map<int,int>* var_id;
std::vector<interval>* elements;

void less_than(interval l, interval r) {
  if (var_id->count(l.id) == 0) {
    elements->push_back(l);
    elements->back().lt_what_list = new std::vector<int>();
    var_id->insert(std::pair<int,int>(l.id, elements->size() - 1));
  }

  if (var_id->count(r.id) == 0) {
    elements->push_back(r);
    elements->back().lt_what_list = new std::vector<int>();
    var_id->insert(std::pair<int,int>(r.id, elements->size() - 1));
  }

  elements->at(var_id->find(l.id)->second).lt_what_list->push_back(var_id->find(r.id)->second);
  elements->at(var_id->find(r.id)->second).predecessor_cnt++;
}

class compare_interval_start {
  public:
  bool operator() (const interval& lhs, const interval& rhs) const
  {
    return (lhs.start < rhs.start);
  }
};

class compare_interval_end {
  public:
  bool operator() (const interval& lhs, const interval& rhs) const
  {
    return (lhs.end < rhs.end);
  }
};

std::priority_queue<interval, std::vector<interval>, compare_interval_end> ready_queue;
std::priority_queue<interval, std::vector<interval>, compare_interval_start> queue;
unsigned int time_ = 0;
unsigned int scheduled_cnt = 0;

void ready_queue_init() {
  for (size_t i = 0; i < elements->size(); i++) {
    if (elements->at(i).predecessor_cnt == 0) {
      queue.push(elements->at(i));
    }
  }

  if (queue.size()) {
    time_ = queue.top().start;

    while (queue.size() && queue.top().start == time_) {
      ready_queue.push(queue.top());
      queue.pop();
    }
  }
}

void ready_queue_update() {
  if (ready_queue.size() == 0 && queue.size() && time_ < queue.top().start)
    time_ = queue.top().start;

  while (queue.size() && queue.top().start <= time_) {
    ready_queue.push(queue.top());
    queue.pop();
  }
}

bool schedule() {
  ready_queue_init();

  while (ready_queue.size()) {
    if (time_ >= ready_queue.top().end)
      return false;

    scheduled_cnt++;
    time_++;
    for (size_t i = 0; i < ready_queue.top().lt_what_list->size(); i++) {
      elements->at(ready_queue.top().lt_what_list->at(i)).predecessor_cnt--;
      if (elements->at(ready_queue.top().lt_what_list->at(i)).predecessor_cnt == 0) {
        queue.push(elements->at(ready_queue.top().lt_what_list->at(i)));
      }
    }

    ready_queue.pop();
    ready_queue_update();
  }

  if (scheduled_cnt < elements->size()) {
    return false;
  }

  return true;
}

void init() {
  var_id   = new std::map<int,int>();
  elements = new std::vector<interval>();
}

int main(int argc, char** argv) {
  interval in1;
  interval in2;
  interval in3;

  init();

  // [start, end)
  in1.start = 1;
  in1.end   = 4;
  in1.id    = 1;
  in1.predecessor_cnt = 0;

  in2.start = 1;
  in2.end   = 4;
  in2.id    = 2;
  in2.predecessor_cnt = 0;

  in3.start = 1;
  in3.end   = 4;
  in3.id    = 3;
  in3.predecessor_cnt = 0;

  less_than(in1, in2);
  less_than(in2, in3);

  std::cout << schedule() << '\n';

  return 0;
}
