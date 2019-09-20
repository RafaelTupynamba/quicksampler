/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dimacs_frontend.cpp

Abstract:

    Frontend for reading dimacs input files

Author:

    Leonardo de Moura (leonardo) 2011-07-26.

Revision History:

--*/
#include<iostream>
#include<unordered_map>
#include<time.h>
#include<signal.h>
#include<vector>
#include "util/timeout.h"
#include "util/rlimit.h"
#include "util/gparams.h"
#include "sat/dimacs.h"
#include "sat/sat_solver.h"

struct cell {
    int c;
    bool v;
};

params_ref p;
reslimit limit;
extern std::vector<int> indsup;
std::unordered_map<std::string, struct cell> hist;
double solver_time = 0.0;
extern bool          g_display_statistics;
static sat::solver * g_solver = nullptr;
static clock_t       g_start_time;

static void display_statistics() {
    clock_t end_time = clock();
    if (g_solver && g_display_statistics) {
        std::cout.flush();
        std::cerr.flush();
        
        statistics st;
        g_solver->collect_statistics(st);
        st.update("total time", ((static_cast<double>(end_time) - static_cast<double>(g_start_time)) / CLOCKS_PER_SEC));
        st.display_smt2(std::cout);
    }
}

static void on_timeout() {
    display_statistics();
    exit(0);
}

static void STD_CALL on_ctrl_c(int) {
    signal (SIGINT, SIG_DFL);
    display_statistics();
    raise(SIGINT);
}

static void display_model(sat::solver const & s) {
    sat::model const & m = s.get_model();
    for (unsigned i = 1; i < m.size(); i++) {
        switch (m[i]) {
        case l_false: std::cout << "-" << i << " ";  break;
        case l_undef: break;
        case l_true: std::cout << i << " ";  break;
        }
    }
    std::cout << "\n";
}

static void display_core(sat::solver const& s, vector<sat::literal_vector> const& tracking_clauses) {
    std::cout << "core\n";
    sat::literal_vector const& c = s.get_core();
    for (unsigned i = 0; i < c.size(); ++i) {
        sat::literal_vector const& cls = tracking_clauses[c[i].var()];
        for (unsigned j = 0; j < cls.size(); ++j) {
            std::cout << cls[j] << " ";
        }
        std::cout << "\n";
    }
}

static void track_clause(sat::solver& dst,
                         sat::literal_vector& lits,
                         sat::literal_vector& assumptions,
                         vector<sat::literal_vector>& tracking_clauses) {
    sat::literal lit = sat::literal(dst.mk_var(true, false), false);
    tracking_clauses.set(lit.var(), lits);
    lits.push_back(~lit);
    dst.mk_clause(lits.size(), lits.c_ptr());
    assumptions.push_back(lit);            
}


static void track_clauses(sat::solver const& src, 
                          sat::solver& dst, 
                          sat::literal_vector& assumptions,
                          vector<sat::literal_vector>& tracking_clauses) {
    for (sat::bool_var v = 0; v < src.num_vars(); ++v) {
        dst.mk_var(false, true);
    }
    sat::literal_vector lits;
    sat::literal lit;
    sat::clause * const * it  = src.begin_clauses();
    sat::clause * const * end = src.end_clauses();
    svector<sat::solver::bin_clause> bin_clauses;
    src.collect_bin_clauses(bin_clauses, false);
    tracking_clauses.reserve(2*src.num_vars() + static_cast<unsigned>(end - it) + bin_clauses.size());

    for (sat::bool_var v = 1; v < src.num_vars(); ++v) {
        if (src.value(v) != l_undef) {
            bool sign = src.value(v) == l_false;
            lits.reset();
            lits.push_back(sat::literal(v, sign));
            track_clause(dst, lits, assumptions, tracking_clauses);
        }
    }
    for (; it != end; ++it) {
        lits.reset();
        sat::clause& cls = *(*it);
        lits.append(static_cast<unsigned>(cls.end()-cls.begin()), cls.begin());
        track_clause(dst, lits, assumptions, tracking_clauses);
    }
    for (unsigned i = 0; i < bin_clauses.size(); ++i) {
        lits.reset();
        lits.push_back(bin_clauses[i].first);
        lits.push_back(bin_clauses[i].second);        
        track_clause(dst, lits, assumptions, tracking_clauses);
    }
}

void verify_solution(char const * file_name) {
    params_ref p = gparams::get_module("sat");
    p.set_bool("produce_models", true);
    reslimit limit;
    sat::solver solver(p, limit);
    std::ifstream in(file_name);
    if (in.bad() || in.fail()) {
        std::cerr << "(error \"failed to open file '" << file_name << "'\")" << std::endl;
        exit(ERR_OPEN_FILE);
    }
    parse_dimacs(in, std::cerr, solver);
    
    sat::model const & m = g_solver->get_model();
    for (unsigned i = 1; i < m.size(); i++) {
        sat::literal lit(i, false);
        switch (m[i]) {
        case l_false: lit.neg(); break;
        case l_undef: break;
        case l_true: break;
        }
        solver.mk_clause(1, &lit);
    }
    lbool r = solver.check();
    switch (r) {
    case l_false: 
        std::cout << "model checking failed\n";
        break;
    case l_true:
        std::cout << "model validated\n";
        break;
    default:
        std::cout << "inconclusive model\n";
        break;
    }
}

double duration(struct timespec * a, struct timespec * b) {
    return (b->tv_sec - a->tv_sec) + 1.0e-9 * (b->tv_nsec - a->tv_nsec);
}

bool check_sample(sat::solver & solver, std::string & line) {
        struct timespec start;
        clock_gettime(CLOCK_REALTIME, &start);

        sat::solver newsolver(p, limit);
        newsolver.copy(solver);
        std::istringstream in(line);
        int nmut;
        in >> nmut;
        char c;
        in >> c;
        in >> c;
        int k = 0;
        while(!in.eof()) {
          sat::literal_vector lits;
          lits.reset();
          if (c == '0') {
            lits.push_back(sat::literal(indsup[k], true));
          } else if (c == '1') {
            lits.push_back(sat::literal(indsup[k], false));
          } else {
            printf("#%c,%d#", c, c);
            abort();
          }
          newsolver.mk_clause(lits.size(), lits.c_ptr());

          in >> c;
          ++k;
        }
        lbool r = newsolver.check();
        bool result = false;
        switch (r) {
          case l_true:
            result = true;
            break;
          case l_undef:
            std::cout << "unknown\n";
            break;
          case l_false:
            break;
        }

        struct timespec end;
        clock_gettime(CLOCK_REALTIME, &end);
        solver_time += duration(&start, &end);
        return result;
}

void quicksampler_check(char const * file_name, sat::solver & solver, double timeout) {
    std::string s(file_name);
    s += ".samples";
    std::ifstream ifs(s);

    int samples = 0;
    int valid[7] = {0};
    int invalid[7] = {0};
    int total[7] = {0};
    struct timespec initial;
    clock_gettime(CLOCK_REALTIME, &initial);
    srand(initial.tv_sec);

    int count = 0;
    int steps = 0;
    p = gparams::get_module("sat");
    p.set_bool("produce_models", true);
    for (std::string line; std::getline(ifs, line); ) {
        ++count;
        check_sample(solver, line);
        if (count == 5) {
            clock_gettime(CLOCK_REALTIME, &initial);
            steps = 0;
        }
        ++steps;
        if (count == 10) break;
    }
    struct timespec current;
    clock_gettime(CLOCK_REALTIME, &current);
    double step = duration(&initial, &current) / steps;
    printf("Step %f s\n", step);

    ifs.clear();
    ifs.seekg(0, std::ios::beg);

    count = 0;
    for (std::string line; std::getline(ifs, line); ) {
        ++count;
        int nmut = line[0] - '0';
        ++total[nmut];
    }

    double probability = 1.0;

    if (timeout != 0.0 && timeout / step < count) {
        probability = (timeout / step) / count;
    }
    printf("Probability %f\n", probability);

    double prob[7] = {0.0};
    for (int i = 0; i < 7; ++i) {
        int min = total[i] < 20 ? total[i] : 20;
        if (total[i] * probability < min) {
            prob[i] = (double)min / (double)total[i];
            printf("prob[%d] = %f\n", i, prob[i]);
        }
    }

    int calls = 0;

    ifs.clear();
    ifs.seekg(0, std::ios::beg);

    clock_gettime(CLOCK_REALTIME, &initial);

    for (std::string line; std::getline(ifs, line); ) {
        int nmut = line[0] - '0';
        bool run1 = rand() <= probability * RAND_MAX;
        bool run2 = false;
        if (prob[nmut])
            run2 = rand() <= prob[nmut] * RAND_MAX;

        bool result;
        if (run1 || run2) {
            auto search = hist.find(line.substr(3));
            if (search != hist.end()) {
                result = search->second.v;
                if (run1) {
                    ++search->second.c;
                }
            } else {
                result = check_sample(solver, line);
                calls += 1;
                struct cell mycell;
                mycell.c = run1? 1 : 0;
                mycell.v = result;
                hist.insert({line.substr(3), mycell});
            }

            if (result) {
                ++valid[nmut];
            } else {
                ++invalid[nmut];
            }
            ++samples;
        }
    }
    ifs.close();
    printf("Mutations\n");
    double all_v = 0.0;
    int all_t = 0;
    for (int i = 0; i < 7; ++ i) {
        printf("%d %d %d %d\n", i, valid[i], invalid[i], total[i]);
        if (valid[i] + invalid[i])
            all_v += (double)total[i] * (double)valid[i] / ((double)valid[i] + invalid[i]);
        all_t += total[i];
    }
    printf("All\n");
    printf("%f / %d = %f\n", all_v, all_t, all_v/all_t);

    std::vector<int> good;
    std::vector<int> bad;
    for (const auto& it : hist) {
        if (it.second.v) {
            if (it.second.c >= good.size())
                good.resize(it.second.c + 1);
            ++good[it.second.c];
        } else {
            if (it.second.c >= bad.size())
                bad.resize(it.second.c + 1);
            ++bad[it.second.c];
        }
    }
    printf("Valid\n");
    count = 0;
    for (auto v : good) {
        printf("%d %d\n", count, v);
        ++count;
    }
    printf("Invalid\n");
    count = 0;
    for (auto v : bad) {
        printf("%d %d\n", count, v);
        ++count;
    }
    clock_gettime(CLOCK_REALTIME, &current);
    double total_time = duration(&initial, &current);
    printf("Total %f s\n", total_time);
    printf("Solver %f s\n", solver_time);
    printf("Checked %d\n", samples);
    printf("Calls %d\n", calls);

    std::string o(file_name);
    o += ".samples.valid";
    std::ofstream ofs(o);
    for (const auto& it : hist) {
        if (it.second.v) {
            const char * sol = it.first.c_str();
            for (int lit : indsup) {
                if (*sol == '0')
                    ofs << '-';
                ofs << lit << ' ';
                ++sol;
            }
            ofs << "0:" << it.second.c << '\n';
        }
    }
    ofs.close();
    exit(0);
}

unsigned read_dimacs(char const * file_name) {
    g_start_time = clock();
    register_on_timeout_proc(on_timeout);
    signal(SIGINT, on_ctrl_c);
    params_ref p = gparams::get_module("sat");
    p.set_bool("produce_models", true);
    reslimit limit;
    sat::solver solver(p, limit);
    g_solver = &solver;

    if (file_name) {
        std::ifstream in(file_name);
        if (in.bad() || in.fail()) {
            std::cerr << "(error \"failed to open file '" << file_name << "'\")" << std::endl;
            exit(ERR_OPEN_FILE);
        }
        parse_dimacs(in, std::cerr, solver);
    }
    else {
        parse_dimacs(std::cin, std::cerr, solver);
    }
    IF_VERBOSE(20, solver.display_status(verbose_stream()););

    if (p.get_bool("quicksampler_check", false)) {
        double timeout = p.get_double("quicksampler_check.timeout", 3600.0);
        quicksampler_check(file_name, solver, timeout);
    }
    
    lbool r;
    vector<sat::literal_vector> tracking_clauses;
    sat::solver solver2(p, limit);
    if (p.get_bool("dimacs.core", false)) {
        g_solver = &solver2;        
        sat::literal_vector assumptions;
        track_clauses(solver, solver2, assumptions, tracking_clauses);
        r = g_solver->check(assumptions.size(), assumptions.c_ptr());
    }
    else {
        r = g_solver->check();
    }
    switch (r) {
    case l_true: 
        std::cout << "sat\n"; 
        if (file_name) verify_solution(file_name);
        display_model(*g_solver);
        break;
    case l_undef: 
        std::cout << "unknown\n"; 
        break;
    case l_false: 
        std::cout << "unsat\n"; 
        if (p.get_bool("dimacs.core", false)) {
            display_core(*g_solver, tracking_clauses);
        }
        break;
    }
    if (g_display_statistics)
        display_statistics();
    return 0;
}
