// Build with minicard/Solver.cc, utils/Options.cc, utils/System.cc and -lz.
// Checks remain active in Release builds.
#include "minicard/Solver.h"
#include "minicard/opb.h"
#include <cstdlib>
#include <iostream>
#include <random>
#include <sstream>
#include <vector>
#include <unistd.h>
using namespace Minisat;

struct Constraint {
    std::vector<int> coefficients;
    int bound;
};

static bool satisfies(const std::vector<Constraint>& constraints, unsigned mask) {
    for (const auto& c : constraints) {
        int sum = 0;
        for (unsigned j = 0; j < c.coefficients.size(); ++j)
            if (mask & (1u << j)) sum += c.coefficients[j];
        if (sum != c.bound) return false;
    }
    return true;
}

static void full_parser() {
    const char* inputs[] = {
        "* root propagation\n+1 x1 >= 1;\n+1 x1 +1 x2 = 1;\n",
        "+1 x1 -1 x1 +1 x2 = 1;\n",
        "+1 x1 +1 x1 +1 x2 = 1;\n",
        "-1 x1 +1 x2 = -1;\n",
        "+1 x1 +1 x2 = 0;\n+1 x1 +1 x2 = 1;\n",
        "* only a comment, no constraints\n"
    };
    unsigned allowed[] = {2,12,4,2,0,15};
    for(unsigned i=0;i<sizeof(allowed)/sizeof(allowed[0]);++i) {
        Solver s;s.newVar();s.newVar();
        FILE* file=tmpfile();if(file==NULL)std::abort();
        fputs(inputs[i],file);rewind(file);
        int fd=dup(fileno(file));if(fd<0)std::abort();
        gzFile stream=gzdopen(fd,"rb");if(stream==NULL)std::abort();
        parse_OPB(stream,s);gzclose(stream);fclose(file);
        for(unsigned mask=0;mask<4;++mask) {
            vec<Lit> as;as.push(mkLit(0,!(mask&1)));as.push(mkLit(1,!(mask&2)));
            if(s.solveLimited(as)!=((allowed[i]&(1u<<mask))?l_True:l_False))std::abort();
        }
    }
}

int main() {
    full_parser();
    {
        Solver s;
        const char* input = "+1 x1 >= 1;";
        readConstr(input, s);
        input = "+1 x1 +1 x2 = 1;";
        readConstr(input, s);
        vec<Lit> as;
        if (s.solveLimited(as) != l_True || s.modelValue(0) != l_True || s.modelValue(1) != l_False)
            return 1;
    }
    std::mt19937 rng(812);
    unsigned checks = 0;
    for (int trial = 0; trial < 2000; ++trial) {
        int n = 1 + rng() % 7;
        unsigned planted = rng() % (1u << n);
        Solver s;
        s.detect_clause = trial % 2;
        for (int j = 0; j < n; ++j) s.newVar();
        std::vector<Constraint> constraints;
        for (int stage = 0; stage < 5; ++stage) {
            Constraint c;
            c.coefficients.assign(n,0);
            c.bound = 0;
            std::ostringstream line;
            int occurrences = trial%2 ? n : 1+rng()%(2*n);
            for (int occurrence = 0; occurrence < occurrences; ++occurrence) {
                int j = trial%2 ? occurrence : rng()%n;
                int coefficient = rng() % 2 ? 1 : -1;
                c.coefficients[j] += coefficient;
                line << (coefficient > 0 ? "+1" : "-1") << " x" << j + 1 << ' ';
                if (planted & (1u << j)) c.bound += coefficient;
            }
            if (trial % 3 == 0) c.bound = int(rng() % (2*n+3)) - n - 1;
            line << "= " << c.bound << ';';
            constraints.push_back(c);
            std::string text = line.str();
            const char* input = text.c_str();
            readConstr(input, s);
            for (unsigned mask = 0; mask < (1u << n); ++mask) {
                vec<Lit> as;
                for (int j = 0; j < n; ++j) as.push(mkLit(j, !(mask & (1u << j))));
                if (s.solveLimited(as) != (satisfies(constraints, mask) ? l_True : l_False)) {
                    std::cerr << "OPB mismatch trial=" << trial << " stage=" << stage << " mask=" << mask << '\n';
                    return 1;
                }
                ++checks;
            }
        }
    }
    std::cout << "PASS OPB assignment checks=" << checks << '\n';
}
