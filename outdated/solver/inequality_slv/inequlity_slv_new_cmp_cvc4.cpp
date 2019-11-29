#include <sys/time.h>
#include <iostream>
#include <fstream>
#include <vector>
#include <queue>
#include <stack>
#include <map>
#include <string>
#include <algorithm>

#include <cvc4/cvc4.h>
using namespace CVC4;

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
    if (node.end < value)
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

  init();

  // ---------------------------------
  // input chars
  // ---------------------------------

  std::vector<std::string> strings;
  std::vector<std::vector<int> > ids;
  unsigned int fuzz = atoi(argv[1]);
  unsigned int cnt = 0;

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

  ///////////////////////////////////////////////////

  // [start, end]
  for (unsigned int i = 0; i < strings.size(); i++) {
    for (unsigned int k = 0; k < i; k++) {
      if (strings.at(i).size() == strings.at(k).size()) {
        for (unsigned int l = 0; l < strings.at(i).size(); l++) {
          in1.start = (int)strings.at(i).at(l) - fuzz;
          in1.end   = (int)strings.at(i).at(l) + fuzz;
          in1.id    = (int)ids.at(i).at(l);
          in1.value = 0;
          in1.predecessor_cnt = 0;
          in2.start = (int)strings.at(k).at(l) - fuzz;
          in2.end   = (int)strings.at(k).at(l) + fuzz;
          in2.id    = (int)ids.at(k).at(l);
          in2.value = 0;
          in2.predecessor_cnt = 0;

          less_than(in1, in2);
        }
      }
    }
  }

  std::cout << "query_1: " << '\n';
  gettimeofday(&tv_begin,NULL);
  std::cout << explore_paths() << '\n';
  gettimeofday(&tv_end,NULL);
  double time_elapsed_in_mcseconds = (tv_end.tv_sec - tv_begin.tv_sec) * 1000000 + (tv_end.tv_usec- tv_begin.tv_usec);
  std::cout << "time: " << time_elapsed_in_mcseconds/1000000 << '\n';

  // ---------------------------------
  // using cvc4 smt solver
  // ---------------------------------

  std::cout << "=========================" << '\n';

  ExprManager em;
  SmtEngine smt(&em);
  smt.setLogic("QF_BV");                         // Set the logic
  smt.setOption("produce-models", true);         // Produce Models
  smt.setOption("incremental", true);
  smt.setOption("bitblast", SExpr("lazy"));      // default is lazy
  smt.setOption("bv-eq-solver", true);           // default is true
  smt.setOption("bv-inequality-solver", true);   // default is true
  Type bitvector32 = em.mkBitVectorType(32);

  cnt = 0;
  std::vector<std::vector<Expr> > strings_bv;
  for (unsigned int i = 0; i < strings.size(); i++) {
    std::vector<Expr> x;
    for (unsigned int j = 0; j < strings.at(i).size(); j++) {
      std::stringstream x_name;
      x_name << "x_" << cnt++;
      x.push_back(em.mkVar(x_name.str().c_str(), bitvector32));
      Expr e1 = em.mkConst(BitVector(32, Integer(strings.at(i).at(j) - fuzz)));
      Expr e2 = em.mkConst(BitVector(32, Integer(strings.at(i).at(j) + fuzz)));
      smt.assertFormula(em.mkExpr(kind::BITVECTOR_UGE, x.back(), e1));
      smt.assertFormula(em.mkExpr(kind::BITVECTOR_ULE, x.back(), e2));
    }
    strings_bv.push_back(x);
  }

  std::cout << "number of init constraints: " << cnt*2 << '\n';
  cnt = 0;
  for (size_t i = 0; i < strings.size(); i++) {
    for (size_t k = 0; k < i; k++) {
      if (strings.at(i).size() == strings.at(k).size()) {
        for (size_t l = 0; l < strings.at(i).size(); l++) {
          smt.assertFormula(em.mkExpr(kind::BITVECTOR_ULT, strings_bv[i][l], strings_bv[k][l]));
          cnt++;
        }
      }
    }
  }

  std::cout << "number of inequality constraints: " << cnt << '\n';

  std::cout << "query_2 cvc4 smt: " << '\n';
  gettimeofday(&tv_begin,NULL);
  std::cout << smt.checkSat() << "\n";
  gettimeofday(&tv_end,NULL);
  time_elapsed_in_mcseconds = (tv_end.tv_sec - tv_begin.tv_sec) * 1000000 + (tv_end.tv_usec- tv_begin.tv_usec);
  std::cout << "time cvc4: " << time_elapsed_in_mcseconds/1000000 << '\n';

  return 0;
}