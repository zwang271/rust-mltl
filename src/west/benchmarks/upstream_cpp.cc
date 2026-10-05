// Timing harness for upstream WEST's C++ (bitset) implementation
// (WEST/src/WEST, the default `bin/west` path). Same output as driver.rs:
// `index<TAB>microseconds<TAB>regexes` per formula, or `index<TAB>skip`
// when the formula needs more than MAXBITS bits.
// Usage: upstream_cpp <file> [start-index]
#include <chrono>
#include <fstream>
#include <iostream>
#include <string>
#include "reg.h"
#include "utils.h"

int main(int argc, char** argv) {
    std::ifstream in(argv[1]);
    int start = argc > 2 ? std::stoi(argv[2]) : 0;
    std::string line;
    for (int i = 0; std::getline(in, line); i++) {
        if (i < start || line.find_first_not_of(" \t") == std::string::npos) continue;
        std::string wff = strip_char(line, ' ');
        std::string nnf = wff_to_nnf(wff);
        int n = get_n(nnf);
        int cl = complen(nnf);
        if (2 * n * cl > MAXBITS) { std::cout << i << "\tskip" << std::endl; continue; }
        auto t0 = std::chrono::steady_clock::now();
        auto r = reg(nnf, n);
        auto us = std::chrono::duration_cast<std::chrono::microseconds>(std::chrono::steady_clock::now() - t0).count();
        std::cout << i << "\t" << us << "\t" << r.size() << std::endl;
    }
}
