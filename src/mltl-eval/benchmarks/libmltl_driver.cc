// Benchmark driver for libmltl (external/libmltl), same CLI and output as
// driver.rs:  libmltl_driver <formulas.txt> <traces.txt> <min_seconds>
#include <chrono>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include "parser.hh"

using namespace libmltl;

static std::vector<std::string> lines(const char *path) {
  std::ifstream in(path);
  std::vector<std::string> out;
  for (std::string l; std::getline(in, l);)
    if (l.find_first_not_of(" \t\r") != std::string::npos) out.push_back(l);
  return out;
}

int main(int argc, char **argv) {
  if (argc != 4) { std::fprintf(stderr, "usage: libmltl_driver <formulas> <traces> <min_seconds>\n"); return 1; }
  std::vector<std::shared_ptr<ASTNode>> formulas;
  for (auto &l : lines(argv[1])) formulas.push_back(parse(l));
  std::vector<std::vector<std::string>> traces;
  for (auto &l : lines(argv[2])) {
    std::istringstream ss(l);
    std::vector<std::string> t;
    for (std::string step; ss >> step;) t.push_back(step);
    traces.push_back(t);
  }
  double min_s = std::stod(argv[3]);
  unsigned long long reps = 0, trues = 0, hash = 0;
  auto start = std::chrono::steady_clock::now();
  double total = 0;
  for (;;) {
    trues = 0;
    hash = 0xcbf29ce484222325ULL;
    for (auto &f : formulas)
      for (auto &t : traces) {
        bool r = f->evaluate(t);
        trues += r;
        hash = (hash ^ (unsigned long long)r) * 0x100000001b3ULL;
      }
    ++reps;
    total = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
    if (total >= min_s) break;
  }
  double evals = (double)reps * formulas.size() * traces.size();
  std::printf("libmltl,%zu,%zu,%llu,%.6f,%.3f,%llu,%016llx\n", formulas.size(), traces.size(), reps, total,
              total * 1e9 / evals, trues, hash);
}
