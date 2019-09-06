#include <iostream>
#include <fstream>
#include <string>
#include <cstdlib>
#include <unordered_map>
#include <boost/filesystem.hpp>

using namespace std;
namespace fs = boost::filesystem;

int main () {
  string orl_1;
  string orl_2;
  string cmd;
  ifstream result_or_oracle_1;
  ifstream result_or_oracle_2;

  fs::path exec_directory = fs::current_path();
  fs::path test_directory("./tests");

  for(auto iter = fs::recursive_directory_iterator(test_directory); iter != fs::recursive_directory_iterator(); ++iter) {
    if (iter->path().extension() == ".c") {
      cmd = "cd " + iter->path().parent_path().string() + "; " + exec_directory.string() + "/selfie -c " + iter->path().filename().string() + " -o " + iter->path().filename().stem().string();
      system(cmd.c_str());
      cmd = "cd " + iter->path().parent_path().string() + "; " + exec_directory.string() + "/phantom -l " + iter->path().filename().stem().string() + " -i 0";
      system(cmd.c_str());
      cmd = "cd " + iter->path().parent_path().string() + "; " + "rm " + iter->path().filename().stem().string();
      system(cmd.c_str());
    }
  }

  std::ofstream output_results("test_output.txt", std::ofstream::trunc);
  unordered_map<string, string> scanned_files;
  unordered_map<string, string>::const_iterator record;
  for(auto iter = fs::recursive_directory_iterator(test_directory); iter != fs::recursive_directory_iterator(); ++iter) {
    record = scanned_files.find(iter->path().filename().stem().string());
    if (record == scanned_files.end()) {
      if (iter->path().filename().extension().string() == ".oracle" || iter->path().filename().extension().string() == ".result") {
        scanned_files.insert(make_pair<string, string>(iter->path().filename().stem().c_str(), iter->path().filename().c_str()));
      }
    } else {
      if (iter->path().filename().extension().string() == ".oracle" || iter->path().filename().extension().string() == ".result") {
        string dir_1 = iter->path().parent_path().string() + "/" + record->second;
        string dir_2 = iter->path().parent_path().string() + "/" + iter->path().filename().string();
        result_or_oracle_1.open(dir_1);
        result_or_oracle_2.open(dir_2);
        if (result_or_oracle_1.is_open() && result_or_oracle_2.is_open()) {
          getline(result_or_oracle_1, orl_1);
          getline(result_or_oracle_2, orl_2);
          while (result_or_oracle_1.eof() == false && result_or_oracle_2.eof() == false) {
            if (orl_2.compare(orl_1) != 0) {
              output_results << "not equal1: " << dir_1 << endl;
              break;
            }
            getline(result_or_oracle_1, orl_1);
            getline(result_or_oracle_2, orl_2);
          }

          if (result_or_oracle_1.eof() == false) {
            output_results << "not equal2: " << dir_1 << endl;
          }

          if (result_or_oracle_2.eof() == false) {
            output_results << "not equal3: " << dir_1 << endl;
          }

          result_or_oracle_1.close();
          result_or_oracle_2.close();
        }
      }
    }
  }

  output_results.close();

  return 0;
}