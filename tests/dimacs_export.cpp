// Compile with minicard/Solver.cc, utils/Options.cc and utils/System.cc.
// Compare every original-variable assignment with its exported CNF extension.
#include "minicard/Solver.h"
#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <random>
#include <sstream>
#include <string>
#include <stdexcept>
#include <vector>
#include <unistd.h>
#ifdef __linux__
#include <dirent.h>
#endif
using namespace Minisat;
struct Constraint { std::vector<int> literals; int bound; bool clause; };
static Lit lit(int x) { return mkLit(std::abs(x)-1, x<0); }
static bool value(int x, unsigned mask) { return bool(mask & (1u<<(std::abs(x)-1))) != (x<0); }
static unsigned checks = 0;
static unsigned exhaustive_tables = 0;
static void require(bool condition) { if (!condition) { std::cerr << "FAIL at check " << checks << '\n'; std::exit(1); } }

static void check(Solver& source, int n, const std::vector<Constraint>& constraints,
                  const std::vector<int>& assumptions, const char* path = NULL) {
    vec<Lit> as;
    for (int x : assumptions) as.push(lit(x));
    if(path!=NULL)source.toDimacs(path,as);
    FILE* file = path==NULL ? tmpfile() : fopen(path,"r");
    require(file != NULL);
    if(path==NULL)source.toDimacs(file, as);
    rewind(file);
    std::string text;
    for (int c; (c = fgetc(file)) != EOF;) text += char(c);
    fclose(file);
    std::istringstream input(text);
    std::string p, kind;
    int variables;
    unsigned long long count;
    require(bool(input >> p >> kind >> variables >> count) && p == "p" && kind == "cnf" && variables >= 0);
    Solver decoded;
    std::vector<std::vector<int>> cnf;
    for (int i = 0; i < std::max(variables,n); ++i) decoded.newVar();
    for (unsigned long long i = 0; i < count; ++i) {
        vec<Lit> clause;
        cnf.push_back({});
        int x;
        do {
            require(bool(input >> x) && x >= -variables && x <= variables);
            if (x) {clause.push(lit(x));cnf.back().push_back(x);}
        } while (x);
        decoded.addClause(clause);
    }
    std::string extra;
    require(!(input >> extra));
    // For small exports, eliminate dependence on *any* SAT engine: enumerate
    // all assignments, including the auxiliary counter variables.
    std::vector<bool> attainable(1u<<n,false);
    if (variables <= 12) {
        ++exhaustive_tables;
        for (unsigned mask=0;mask<(1u<<std::max(variables,n));++mask) {
            bool valid=true;
            for (const auto& clause:cnf) {
                bool satisfied=false;
                for(int x:clause)satisfied|=value(x,mask);
                if(!satisfied){valid=false;break;}
            }
            if(valid)attainable[mask&((1u<<n)-1)]=true;
        }
    }
    for (unsigned mask = 0; mask < (1u << n); ++mask) {
        bool expected = true;
        for (int x : assumptions) expected &= value(x,mask);
        for (const auto& c : constraints) {
            int sum = 0;
            for (int x : c.literals) sum += value(x,mask);
            expected &= c.clause ? sum > 0 : sum <= c.bound;
        }
        vec<Lit> fixed;
        for (int j = 0; j < n; ++j) fixed.push(mkLit(j, !(mask & (1u << j))));
        ++checks;
        require(decoded.solveLimited(fixed) == (expected ? l_True : l_False));
        if(variables<=12)require(attainable[mask]==expected);
    }
}

static void add(Solver& s, const Constraint& c) {
    vec<Lit> literals;
    for (int x : c.literals) literals.push(lit(x));
    if (c.clause) s.addClause(literals); else s.addAtMost(literals,c.bound);
}

#ifdef __linux__
static unsigned descriptor_count() {
    DIR* dir=opendir("/proc/self/fd");require(dir!=NULL);
    unsigned count=0;while(readdir(dir)!=NULL)++count;
    closedir(dir);return count;
}
#endif

static void filename_api() {
    char path[]="minicard-export-test-XXXXXX";
    int fd=mkstemp(path);require(fd>=0);close(fd);
    Solver s;for(int i=0;i<3;++i)s.newVar();
    std::vector<Constraint> constraints{{{1,2,3},1,false}};add(s,constraints[0]);
    check(s,3,constraints,{},path);check(s,3,constraints,{3},path);
#ifdef __linux__
    unsigned before=descriptor_count();
#endif
    vec<Lit> invalid;invalid.push(mkLit(3));
    for(int i=0;i<64;++i) {
        bool rejected=false;
        try{s.toDimacs(path,invalid);}catch(const std::out_of_range&){rejected=true;}
        require(rejected);
    }
#ifdef __linux__
    bool closed=descriptor_count()==before;
#endif
    require(unlink(path)==0);
#ifdef __linux__
    require(closed);
#endif
}

int main() {
    filename_api();
    {
        Solver empty;check(empty,0,{},{});
        Solver root;for(int i=0;i<3;++i)root.newVar();
        std::vector<Constraint> constraints{{{3},0,true}};
        add(root,constraints[0]);root.simplify();
        check(root,3,constraints,{});check(root,3,constraints,{-3});
    }
    for (int bound = -1; bound <= 5; ++bound) {
        Solver s;
        s.detect_clause = false;
        for (int j = 0; j < 4; ++j) s.newVar();
        std::vector<Constraint> constraints{{{1,1,-2,3},bound,false}};
        add(s,constraints[0]);
        check(s,4,constraints,{});
        vec<Lit> old; old.push(mkLit(3)); s.solveLimited(old);
        check(s,4,constraints,{-4}); // export argument must override the last solve's assumptions
        check(s,4,constraints,{4,-4});
    }
    std::mt19937 rng(987612);
    for (int trial = 0; trial < 1000; ++trial) {
        int n = 1 + rng()%7;
        unsigned planted = rng()%(1u<<n);
        Solver s;
        s.detect_clause = trial%2;
        for (int j = 0; j < n; ++j) s.newVar();
        std::vector<Constraint> constraints;
        for (int stage = 0; stage < 8; ++stage) {
            Constraint c{{},0,rng()%3==0};
            int length = rng()%(2*n+1), sum = 0;
            for (int j = 0; j < length; ++j) {
                int x = (1+int(rng()%n))*(rng()%2?1:-1);
                c.literals.push_back(x); sum += value(x,planted);
            }
            c.bound = trial%2 ? sum : int(rng()%(length+3))-1;
            if (trial%2 && c.clause && sum == 0) c.literals.push_back(planted&1 ? 1 : -1);
            constraints.push_back(c); add(s,c);
            vec<Lit> old; old.push(mkLit(0)); s.solveLimited(old);
            if (s.okay()) s.garbageCollect();
            check(s,n,constraints,{stage%2 ? 1 : -1});
        }
    }
    std::cout << "PASS DIMACS assignment checks=" << checks << " independent truth tables=" << exhaustive_tables << '\n';
}
