#include <z3++.h>
#include <vector>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <fstream>

class QuickSampler {
    std::string input_file;

    struct timespec start_time;
    double solver_time = 0.0;

    z3::context c;
    z3::optimize opt;
    std::vector<int> ind;
    std::unordered_set<int> unsat_vars;
    int epochs = 0;
    int flips = 0;
    int samples = 0;
    int solver_calls = 0;

    std::ofstream results_file;

public:
    QuickSampler(std::string input) : opt(c), input_file(input) {}

    void run() {
        clock_gettime(CLOCK_REALTIME, &start_time);
        srand(start_time.tv_sec);
        parse_cnf();
        results_file.open(input_file + ".samples");
        while (true) {
            opt.push();
            for (int v : ind) {
                if (rand() % 2)
                    opt.add(literal(v), 1);
                else
                    opt.add(!literal(v), 1);
            }
            if (!solve())
                break;
            z3::model m = opt.get_model();
            opt.pop();

            sample(m);
            print_stats(false);
        }
    }

    void print_stats(bool simple) {
        struct timespec end;
        clock_gettime(CLOCK_REALTIME, &end);
        double elapsed = duration(&start_time, &end);
        std::cout << "Samples " << samples << '\n';
        std::cout << "Execution time " << elapsed << '\n';
        if (simple)
            return;
        std::cout << "Solver time: " << solver_time << '\n';
        std::cout << "Epochs " << epochs << ", Flips " << flips << ", Unsat " << unsat_vars.size() << ", Calls " << solver_calls << '\n';
    }

    void parse_cnf() {
        z3::expr_vector exp(c);
        std::ifstream f(input_file);
        if (!f.is_open()) {
            std::cout << "Error opening input file\n";
            abort();
        }
        std::string line;
        while (getline(f, line)) {
            std::istringstream iss(line);
            if(line.find("c ind ") == 0) {
                std::string s;
                iss >> s;
                iss >> s;
                int v;
                while (!iss.eof()) {
                    iss >> v;
                    if (v)
                        ind.push_back(v);
                }
            } else if (line[0] != 'c' && line[0] != 'p') {
                z3::expr_vector clause(c);
                int v;
                while (!iss.eof()) {
                    iss >> v;
                    if (v > 0)
                        clause.push_back(literal(v));
                    else if (v < 0)
                        clause.push_back(!literal(-v));
                }
                exp.push_back(mk_or(clause));
            }
        }
        f.close();
        z3::expr formula = mk_and(exp);
        opt.add(formula);
    }

    void sample(z3::model m) {
        std::unordered_set<std::string> initial_mutations;
        std::string m_string = model_string(m);
        std:: cout << m_string << " STARTING\n";
        output(m_string, 0);
        opt.push();
        for (int i = 0; i < ind.size(); ++i) {
            int v = ind[i];
            if (m_string[i] == '1')
                opt.add(literal(v), 1);
            else
                opt.add(!literal(v), 1);
        }

        std::unordered_map<std::string, int> mutations;
        for (int i = 0; i < ind.size(); ++i) {
            if (unsat_vars.find(i) != unsat_vars.end())
                continue;
            opt.push();
            int v = ind[i];
            if (m_string[i] == '1')
                opt.add(!literal(v));
            else
                opt.add(literal(v));
            if (solve()) {
                z3::model new_model = opt.get_model();
                std::string new_string = model_string(new_model);
                if (initial_mutations.find(new_string) == initial_mutations.end()) {
                    initial_mutations.insert(new_string);
                    //std::cout << new_string << '\n';
                    std::unordered_map<std::string, int> new_mutations;
                    new_mutations[new_string] = 1;
                    output(new_string, 1);
                    flips += 1;
                    for (auto it : mutations) {
                        if (it.second >= 6)
                            continue;
                        std::string candidate;
                        for (int j = 0; j < ind.size(); ++j) {
                            bool a = m_string[j] == '1';
                            bool b = it.first[j] == '1';
                            bool c = new_string[j] == '1';
                            if (a ^ ((a^b) | (a^c)))
                                candidate += '1';
                            else
                                candidate += '0';
                        }
                        if (mutations.find(candidate) == mutations.end() && new_mutations.find(candidate) == new_mutations.end()) {
                            new_mutations[candidate] = it.second + 1;
                            output(candidate, it.second + 1);
                        }
                    }
                    for (auto it : new_mutations) {
                        mutations[it.first] = it.second;
                    }
                } else {
                    //std::cout << new_string << " repeated\n";
                }
            } else {
                std::cout << "unsat\n";
                unsat_vars.insert(i);
            }
            opt.pop();
            print_stats(true);
        }
        epochs += 1;
        opt.pop();
    }

    void output(std::string sample, int nmut) {
        samples += 1;
        results_file << nmut << ": " << sample << '\n';
    }

    void finish() {
        print_stats(false);
        results_file.close();
        exit(0);
    }

    bool solve() {
        struct timespec start;
        clock_gettime(CLOCK_REALTIME, &start);
        double elapsed = duration(&start_time, &start);
        if (elapsed > 2 * 3600) {
            std::cout << "Stopping: timeout\n";
            finish();
        }
        if (samples >= 10000000) {
            std::cout << "Stopping: samples\n";
            finish();
        }

        z3::check_result result = opt.check();
        struct timespec end;
        clock_gettime(CLOCK_REALTIME, &end);
        solver_time += duration(&start, &end);
        solver_calls += 1;

        return result == z3::sat;
    }

    std::string model_string(z3::model model) {
        std::string s;

        for (int v : ind) {
            z3::func_decl decl(literal(v).decl());
            z3::expr b = model.get_const_interp(decl);
            if (b.bool_value() == Z3_L_TRUE) {
                s += "1";
            } else {
                s += "0";
            }
        }
        return s;
    }


    double duration(struct timespec * a, struct timespec * b) {
        return (b->tv_sec - a->tv_sec) + 1.0e-9 * (b->tv_nsec - a->tv_nsec);
    }

    z3::expr literal(int v) {
        return c.constant(c.str_symbol(std::to_string(v).c_str()), c.bool_sort());
    }
};

int main(int argc, char * argv[]) {
    if (argc < 2) {
        std::cout << "Argument required: input file\n";
        abort();
    }
    QuickSampler s(argv[1]);
    s.run();
    return 0;
}
