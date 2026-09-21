// Independent truth-table audit of the native MiniCard API.
#include "minicard/Solver.h"
#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <random>
#include <string>
#include <vector>
using namespace Minisat;
struct Constraint { std::vector<int> lits; int bound; bool clause; };
static unsigned long queries = 0;
static Lit literal(int x) { return mkLit(std::abs(x)-1, x<0); }
static bool bit(int x, unsigned mask) { return bool(mask & (1u << (std::abs(x)-1))) != (x<0); }
static bool accepts(const std::vector<Constraint>& cs, const std::vector<int>& assumptions, unsigned mask) {
    for (int l: assumptions) if (!bit(l,mask)) return false;
    for (const auto& c: cs) {
        int count=0; for(int l:c.lits) count+=bit(l,mask);
        if (c.clause ? count==0 : count>c.bound) return false;
    }
    return true;
}
static void add(Solver& s,const Constraint& c) {
    vec<Lit> ls; for(int l:c.lits)ls.push(literal(l));
    if(c.clause)s.addClause(ls);else s.addAtMost(ls,c.bound);
}
static void check(Solver& s,int n,const std::vector<Constraint>& cs,const std::vector<int>& assumptions) {
    bool expected=false;
    for(unsigned m=0;m<(1u<<n);++m) if(accepts(cs,assumptions,m)){expected=true;break;}
    vec<Lit> as;for(int l:assumptions)as.push(literal(l));
    lbool result=s.solveLimited(as); ++queries;
    bool valid=result==(expected?l_True:l_False);
    if(result==l_True) {
        unsigned model=0;for(int i=0;i<n;++i) {
            if(s.modelValue(i)==l_Undef)valid=false;
            if(s.modelValue(i)==l_True)model|=1u<<i;
        }
        valid=valid&&accepts(cs,assumptions,model);
    }
    if(!valid) {
        std::cerr<<"FAIL query="<<queries<<" n="<<n<<" expected="<<expected<<" result="<<toInt(result)<<'\n';
        for(const auto& c:cs){for(int l:c.lits)std::cerr<<l<<' ';std::cerr<<(c.clause?"clause":"<=")<<' '<<c.bound<<'\n';}
        std::cerr<<"assume ";for(int l:assumptions)std::cerr<<l<<' ';std::cerr<<'\n';std::exit(1);
    }
}
static void random_api(int mode,int trials,unsigned seed) {
    std::mt19937 rng(seed);
    for(int t=0;t<trials;++t) {
        int n=2+rng()%8;unsigned planted=rng()%(1u<<n);Solver s;s.ccmin_mode=mode;s.restart_first=2;s.garbage_frac=0;
        s.detect_clause=t%2;
        for(int i=0;i<n;++i)s.newVar();
        std::vector<Constraint> cs;
        for(int stage=0;stage<18;++stage) {
            Constraint c{{},0,rng()%3==0};int count=rng()%(2*n+1);
            for(int j=0;j<count;++j)c.lits.push_back((1+int(rng()%n))*(rng()%2?1:-1));
            c.bound=int(rng()%(count+3))-1;
            if(t%2) {
                int true_count=0;for(int l:c.lits)true_count+=bit(l,planted);
                if(c.clause&&true_count==0)c.lits.push_back((rng()%n+1));
                if(c.clause&&!accepts({c},{},planted))c.lits.back()=-c.lits.back();
                if(!c.clause)c.bound=std::max(c.bound,true_count);
            }
            cs.push_back(c);add(s,c);
            for(int q=0;q<4;++q) {
                std::vector<int> as;
                for(int j=0;j<n;++j)if(rng()%3==0)as.push_back((j+1)*(rng()%2?1:-1));
                check(s,n,cs,as);
            }
            if(s.okay()) {s.garbageCollect();check(s,n,cs,{});}
        }
    }
}
static void intervals(int mode) {
    std::mt19937 rng(31);
    for(int n=1;n<=9;++n)for(int trial=0;trial<20;++trial) {
        Solver s;s.ccmin_mode=mode; for(int j=0;j<n;++j)s.newVar();
        std::vector<std::pair<Var,Var>> guards;
        for(int k=0;k<=n;++k) {
            Var hi=s.newVar(),lo=s.newVar();guards.push_back({hi,lo});
            vec<Lit> upper,lower;
            for(int j=0;j<n;++j){upper.push(mkLit(j));lower.push(~mkLit(j));}
            for(int j=0;j<n-k;++j)upper.push(mkLit(hi));
            for(int j=0;j<k;++j)lower.push(mkLit(lo));
            s.addAtMost(upper,n);s.addAtMost(lower,n);
        }
        std::vector<Constraint> cover;
        for(int stage=0;stage<24;++stage) {
            if(stage) {
                Constraint c{{},0,true};
                for(int j=0;j<n;++j){int v=rng()%3;if(v<2)c.lits.push_back((j+1)*(v?1:-1));}
                cover.push_back(c);add(s,c);
            }
            for(int t=0;t<=n;++t) {
                int k=stage%2?n-t:t;vec<Lit> as;
                for(int j=0;j<=n;++j){as.push(mkLit(guards[j].first,j!=k));as.push(mkLit(guards[j].second,j!=k));}
                bool expected=false;
                for(unsigned m=0;m<(1u<<n);++m)if(__builtin_popcount(m)==k&&accepts(cover,{},m)){expected=true;break;}
                lbool got=s.solveLimited(as);++queries;
                if(got!=(expected?l_True:l_False)){std::cerr<<"INTERVAL FAIL n="<<n<<" stage="<<stage<<" k="<<k<<'\n';std::exit(1);}
                if(got==l_True){unsigned m=0;for(int j=0;j<n;++j)if(s.modelValue(j)==l_True)m|=1u<<j;
                    if(__builtin_popcount(m)!=k||!accepts(cover,{},m))std::abort();}
            }
            if(s.okay())s.garbageCollect();
        }
    }
}
static void multisets(int mode, std::vector<int>& literals, int first = 0) {
    for (int bound = -1; bound <= int(literals.size())+1; ++bound) for (int detect = 0; detect < 2; ++detect) {
        Solver s;s.ccmin_mode=mode;s.detect_clause=detect;
        for(int i=0;i<3;++i)s.newVar();
        std::vector<Constraint> cs{{literals,bound,false}};add(s,cs[0]);check(s,3,cs,{});
        for(unsigned mask=0;mask<8;++mask) {
            std::vector<int> as;
            for(int i=0;i<3;++i)as.push_back((mask&(1u<<i))?i+1:-(i+1));
            check(s,3,cs,as);
        }
    }
    if(literals.size()==6)return;
    for(int i=first;i<6;++i) {
        literals.push_back((i%2?-1:1)*(i/2+1));
        multisets(mode,literals,i);literals.pop_back();
    }
}
static void edge_api(int mode) {
    Solver s;for(int i=0;i<4;++i)s.newVar();vec<Lit> ps;ps.push(mkLit(0));ps.push(mkLit(1));ps.push(mkLit(2));
    s.ccmin_mode=mode;
    s.addAtMost(ps,1);
    vec<Lit> as;s.interrupt();
    if(s.solveLimited(as)!=l_Undef||!s.okay())std::abort();
    s.clearInterrupt();s.setConfBudget(0);
    if(s.solveLimited(as)!=l_Undef||!s.okay())std::abort();
    s.budgetOff();if(s.solveLimited(as)!=l_True)std::abort();queries+=3;
    for(int n:{35,64,65,100,129})for(int k:{0,1,n/2,n-1,n}) {
        Solver w;w.ccmin_mode=mode;vec<Lit> a,b;for(int i=0;i<n;++i){w.newVar();a.push(mkLit(i));b.push(~mkLit(i));}
        w.addAtMost(a,k);w.addAtMost(b,n-k);vec<Lit> none;
        if(w.solveLimited(none)!=l_True)std::abort();int count=0;for(int i=0;i<n;++i)count+=w.modelValue(i)==l_True;
        if(count!=k)std::abort();w.garbageCollect();if(w.solveLimited(none)!=l_True)std::abort();
        ++queries;
    }
}
int main(int argc,char**argv) {
    int mode=argc>1?std::atoi(argv[1]):2,trials=argc>2?std::atoi(argv[2]):2000;
    if(mode<0||mode>2||trials<0)return 2;
    unsigned seed=argc>3?std::strtoul(argv[3],NULL,10):20260908u;
    std::vector<int> literals;
    random_api(mode,trials,seed);intervals(mode);edge_api(mode);multisets(mode,literals);
    std::cout<<"PASS queries="<<queries<<" ccmin="<<mode<<" trials="<<trials<<" seed="<<seed<<'\n';
}
