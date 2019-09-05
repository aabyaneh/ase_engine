#include <iostream>
#include <fstream>
#include <string>

using namespace std;

int main () {
  string rl;
  string ol;

  ifstream result ("results.txt");
  ifstream oracle ("oracles.txt");

  if (result.is_open() && oracle.is_open()) {
    while (getline(oracle, ol)) {
      getline(result, rl);
      if (rl.compare(ol) != 0) {
        cout << "not equal \n";
        break;
      }
    }
    result.close();
    oracle.close();
  }

  return 0;
}