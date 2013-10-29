/*********************************************************************
Author: Soonho Kong <soonhok@cs.cmu.edu>
        Sicun Gao <sicung@cs.cmu.edu>
        Edmund Clarke <emc@cs.cmu.edu>

dReal -- Copyright (C) 2013, Soonho Kong, Sicun Gao, and Edmund Clarke

dReal is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

dReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with dReal. If not, see <http://www.gnu.org/licenses/>.
*********************************************************************/

#include "dsolvers/icp_solver.h"
#include "dsolvers/util/scoped_env.h"
#include "dsolvers/util/scoped_vec.h"
#include <iomanip>
#include <string>
#include <thread>
#include <boost/algorithm/string/predicate.hpp>

using boost::starts_with;

icp_solver::icp_solver(SMTConfig& c, scoped_vec const & stack, scoped_env & env,
                       vector<Enode*> & exp, map <Enode*, set<Enode*>> & enode_to_vars)
    : _config(c), _propag(nullptr), _boxes(env.size()), _ep(nullptr), _sol(0), _nsplit(0),
      _enode_to_vars(enode_to_vars), _explanation(exp), m_stack(stack), m_env(env),
      num_ode_groups(1), diff_vec(1), ode_solvers(1) {
    rp_init_library();
    _problem = create_rp_problem();
    _propag = new rp_propagator(_problem, 10.0, c.nra_verbose, c.nra_proof_out);

    //rp_new(_vselect, rp_selector_roundrobin, (_problem));
    rp_new(_vselect, rp_selector_existence, (_problem));
    // rp_new(_dsplit, rp_splitter_mixed, (_problem));
    rp_new(_dsplit, rp_splitter_bisection, (_problem));
    // Check once the satisfiability of all the constraints
    // Necessary for variable-free constraints
    int i = 0, sat = 1;
    while ((i < rp_problem_nctr(*_problem)) && (sat)) {
        if (rp_constraint_unfeasible(rp_problem_ctr(*_problem, i), rp_problem_box(*_problem))) {
            sat = 0;
        } else {
            ++i;
        }
    }

    if (sat) {
        // Insertion of the initial box in the search structure
        _boxes.insert(rp_problem_box(*_problem));

        // Management of improvement factor
        if ((c.nra_icp_improve >= 0.0) && (c.nra_icp_improve <= 100.0)) {
            _improve = 1.0 - c.nra_icp_improve / 100.0;
        } else {
            _improve = 0.875; /* 12.5% */
        }
        _propag->set_improve(_improve);

        // Creation of the operators and insertion in the propagator
        rp_hybrid_factory hfact(_improve);
        hfact.apply(_problem, *_propag);

        rp_domain_factory dfact;
        dfact.apply(_problem, *_propag);

        rp_newton_factory nfact(_improve);
        nfact.apply(_problem, *_propag);

        // rp_3b_factory bfact(_improve);
        // bfact.apply(p,_propag);

        // Used for round-robin strategy: last variable split
        rp_box_set_split(_boxes.get(), -1);// sean: why is the last variable -1? oh, must be length - this number
    } else {
        rp_box_set_empty(rp_problem_box(*_problem));
    }

    if (_config.nra_contain_ODE) {
        create_ode_solvers();
    }
}

icp_solver::~icp_solver() {
    rp_delete(_vselect);
    rp_delete(_dsplit);
    rp_reset_library();
    delete _propag;
    for (rp_variable * _v : _rp_variables) {
        delete _v;
    }
    for (rp_constraint * _c : _rp_constraints) {
        delete _c;
    }
    for (ode_solver * _s : ode_solvers) {
        delete _s;
    }
    rp_problem_destroy(_problem);
    delete _problem;
}

void icp_solver::create_ode_solvers() {
    // 1. Collect All the ODE Vars
    // For each enode in the stack
    for (auto stack_ite = m_stack.cbegin(); stack_ite != m_stack.cend(); stack_ite++) {
        set<Enode*> ode_vars = _enode_to_vars[*stack_ite];
        for (auto ite = ode_vars.begin(); ite != ode_vars.end(); ite++) {
            unsigned diff_group = (*ite)->getODEgroup();
            if (_config.nra_verbose) {
                cerr << "ode_var: " << *ite << endl;
                cerr << "diff_group: " << diff_group << ", num_ode_groups: " << num_ode_groups << endl;
            }
            if (diff_group>= num_ode_groups) {
                if (_config.nra_verbose) {
                    cerr << "diff_group: " << diff_group << " we do resize" << endl;
                }
                diff_vec.resize(diff_group + 1);
                num_ode_groups = diff_group;
                if (_config.nra_verbose) {
                    cerr << "num_ode_groups: " << num_ode_groups << endl;
                }
            }
            if (diff_vec[diff_group].empty()) {
                if (_config.nra_verbose) {
                    cerr << "diff_vec[" << diff_group << "] is empty!!" << endl;
                }
            }
            diff_vec[diff_group].insert(*ite);
            if (_config.nra_verbose) {
                cerr << "diff_group inserted: " << diff_group << endl;
            }
        }
    }
    ode_solvers.resize(num_ode_groups + 1);
    for (unsigned g = 0; g <= num_ode_groups; g++) {
        if (!diff_vec[g].empty()) {
            ode_solvers[g] = new ode_solver(g, _config, diff_vec[g], _boxes.get(), _enode_to_rp_id);
        }
    }
}

rp_problem* icp_solver::create_rp_problem() {
    rp_problem* rp_prob = new rp_problem;
    rp_problem_create(rp_prob, "icp_holder");

    // ======================================
    // Create rp_variable for each var in env
    // ======================================
    for (auto ite = m_env.begin(); ite != m_env.end(); ite++) {
        Enode* key = (*ite).first;
        const double lb = (*ite).second.first;
        const double ub = (*ite).second.second;

        rp_variable * _v = new rp_variable;
        _rp_variables.push_back(_v);
        string name = key->getCar()->getName();
        rp_variable_create(_v, name.c_str());
        int rp_id = rp_vector_insert(rp_table_symbol_vars(rp_problem_symb(*rp_prob)), *_v);
        rp_box_enlarge_size(&rp_problem_box (*rp_prob), 1);
        rp_bsup(rp_box_elem(rp_problem_box(*rp_prob), rp_id)) = ub;
        rp_binf(rp_box_elem(rp_problem_box(*rp_prob), rp_id)) = lb;
        rp_union_interval u;
        rp_union_create(&u);
        rp_union_insert(u, rp_box_elem(rp_problem_box(*rp_prob), rp_id));
        rp_union_copy(rp_variable_domain(*_v), u);
        rp_union_destroy(&u);

        // rp_variable_set_real(*_v);
        // rp_variable_precision(*_v) = _config.nra_precision;
        _enode_to_rp_id[key] = rp_id;
        if (_config.nra_verbose) {
            cerr << "Key: " << name << "\t"
                 << "value : [" << lb << ", " << ub << "] \t"
                 << "precision : " << _config.nra_precision << "\t"
                 << "rp_id: " << rp_id << endl;
        }
    }

    // ===============================================
    // Create rp_constraints for each literal in stack
    // ===============================================
    for (auto ite = m_stack.cbegin(); ite != m_stack.cend(); ite++) {
        Enode* l = *ite;
        stringstream buf;
        rp_constraint * _c = new rp_constraint;
        _rp_constraints.push_back(_c);
        l->print_infix(buf, l->getPolarity());
        string constraint_str = buf.str();

        if (constraint_str.compare("0 = 0") != 0) {
            if (_config.nra_verbose) {
                cerr << "Constraint: "
                     << (l->getPolarity() == l_True ? " " : "Not")
                     << l << endl;
                cerr << " : " << constraint_str << endl;
            }

            // Parse the string (infix form) to create the constraint _c
            rp_parse_constraint_string(_c, constraint_str.c_str(), rp_problem_symb(*rp_prob));

            // Add to the problem
            rp_vector_insert(rp_problem_ctrs(*rp_prob), *_c);

            // Update Counter
            for (int i = 0; i <rp_constraint_arity(*_c); ++i) {
                ++rp_variable_constrained(rp_problem_var(*rp_prob, rp_constraint_var(*_c, i)));
            }
        }
    }
    return rp_prob;
}

bool icp_solver::callODESolver(int group, set<Enode*> const & ode_vars, bool forward) {
    if (_config.nra_verbose) {
        cerr << "solve ode group: " << group << endl;
    }

    // The size of ODE_Vars should be even
    if (ode_vars.size() % 2 == 1) {
        if (_config.nra_verbose) {
            cerr << "The size of ODE_Vars should be even" << endl;
            for (auto ode_var : ode_vars) {
                cerr << ode_var << endl;
            }
        }
        return false;
    }

    // If the _0 and _t variables do not match, return false.
    for (auto ite = ode_vars.cbegin(); ite != ode_vars.cend(); ite++) {
        if (ode_vars.find((*ite)->getODEopposite()) == ode_vars.end()) {
            if (_config.nra_verbose) {
                cerr << "the _0 and _t variables do not match:" << *ite << endl;
            }
            return false;
        }
    }

    if (!ode_vars.empty()) {
        if (_config.nra_verbose) {
            cerr << "Inside of current ODEs" << endl;
        }
        if (_config.nra_verbose) {
            for (auto ode_var : ode_vars) {
                cerr << "Name: " << ode_var->getCar()->getName() << endl;
            }
        }
        ode_solver* odeSolver = ode_solvers[group];

        if(forward) {
            bool simple_ODE = odeSolver->simple_ODE(_boxes.get()) && _propag->apply(_boxes.get());
            if(!simple_ODE) return false;

            bool forward_ODE = true;
            bool forward_exception = false;
            try {
                forward_ODE = odeSolver->solve_forward(_boxes.get()) && _propag->apply(_boxes.get());
            }
            catch(exception& e) {
                if (_config.nra_verbose) {
                    cerr << "Exception in ODE Solving (Forward)" << endl
                         << e.what() << endl;
                }
                forward_exception = true;
            }
            if(!forward_exception) return forward_ODE;
            try {
                return odeSolver->solve_backward(_boxes.get()) && _propag->apply(_boxes.get());
            }
            catch(exception& e) {
                if (_config.nra_verbose) {
                    cerr << "Exception in ODE Solving (Backward)" << endl
                         << e.what() << endl;
                }
                return true;
            }
        } else {
            bool simple_ODE = odeSolver->simple_ODE(_boxes.get()) && _propag->apply(_boxes.get());
            if(!simple_ODE) return false;

            bool backward_ODE = true;
            bool backward_exception = false;
            try {
                backward_ODE = odeSolver->solve_backward(_boxes.get()) && _propag->apply(_boxes.get());
            }
            catch(exception& e) {
                if (_config.nra_verbose) {
                    cerr << "Exception in ODE Solving (Backward)" << endl
                         << e.what() << endl;
                }
                backward_exception = true;
            }
            if(!backward_exception) return backward_ODE;
            try {
                return odeSolver->solve_forward(_boxes.get()) && _propag->apply(_boxes.get());
            }
            catch(exception& e) {
                if (_config.nra_verbose) {
                    cerr << "Exception in ODE Solving (Forward)" << endl
                         << e.what() << endl;
                }
                return true;
            }
        }
    }
    return true;
}

bool icp_solver::is_atomic(set<Enode*> const & ode_vars, double const p) {
    rp_box _b = _boxes.get();
    for(auto ode_var : ode_vars) {
        double lb = rp_binf(rp_box_elem(_b, _enode_to_rp_id[ode_var]));
        double ub = rp_bsup(rp_box_elem(_b, _enode_to_rp_id[ode_var]));
        if (ub - lb > p) {
            return false;
        }
    }
    return true;
}

vector<pair<double, double>> icp_solver::measure_size(set<Enode*> const & ode_vars, double const prec) {
    rp_box const & _b = _boxes.get();
    vector<pair<Enode*, Enode*>> ode_pairs;

    // extract ode pairs
    for(auto ode_var : ode_vars) {
        lbool const & odeType = ode_var->getODEvartype();
        if (odeType == l_False) {
            ode_pairs.push_back(make_pair(ode_var, ode_var->getODEopposite()));
        }
    }
    // sort ode_pairs by their rp_id
    std::sort(ode_pairs.begin(), ode_pairs.end(), [this](pair<Enode*, Enode*> const p1, pair<Enode*, Enode*> const p2) {
            return _enode_to_rp_id[p1.first] < _enode_to_rp_id[p2.first];
        });

    // extract width
    vector<pair<double, double>> ret;
    for(auto p : ode_pairs) {
        double const lb_0 = rp_binf(rp_box_elem(_b, _enode_to_rp_id[p.first]));
        double const ub_0 = rp_bsup(rp_box_elem(_b, _enode_to_rp_id[p.first]));
        double const s_0 = max(ub_0 - lb_0, prec);
        double const lb_t = rp_binf(rp_box_elem(_b, _enode_to_rp_id[p.second]));
        double const ub_t = rp_bsup(rp_box_elem(_b, _enode_to_rp_id[p.second]));
        double const s_t = max(ub_t - lb_t, prec);
        ret.push_back(make_pair(s_0, s_t));
    }
    return ret;
}


bool icp_solver::prop_with_ODE() {
    if (_propag->apply(_boxes.get())) {
        if (_config.nra_contain_ODE) {
            // Find ODE groups whose X_0, X_t, and T are smallest interval boxes
            vector<pair<unsigned, pair<double, double>>> ode_group_scores;
            for (unsigned i = 1; i <= num_ode_groups; i++) {
                if (!diff_vec[i].empty()) {
                    ode_group_scores.push_back(make_pair(i, make_pair(0.0, 0.0)));
                }
            }

            auto ratio_comp = [](pair<double, double> const & x, pair<double, double> const & y) {
                double const x_0 = x.first;
                double const x_t = x.second;
                double const x_r = x_t > x_0 ? x_t / x_0 : x_0 / x_t;
                double const y_0 = y.first;
                double const y_t = y.second;
                double const y_r = y_t > y_0 ? y_t / y_0 : y_0 / y_t;
                return x_r < y_r;
            };

            auto diff_comp = [](pair<double, double> const & x, pair<double, double> const & y) {
                double const x_0 = x.first;
                double const x_t = x.second;
                double const x_r = x_t > x_0 ? x_t - x_0 : x_0 - x_t;
                double const y_0 = y.first;
                double const y_t = y.second;
                double const y_r = y_t > y_0 ? y_t - y_0 : y_0 - y_t;
                return x_r < y_r;
            };

            auto compute_max_width = [this, &ratio_comp](set<Enode*> const & vars, double const prec) {
                vector<pair<double, double>> s = measure_size(vars, prec);
                return *max_element(s.begin(), s.end(), ratio_comp);
            };

            auto compute_volume = [this](set<Enode*> const & vars, double const prec) {
                vector<pair<double, double>> s = measure_size(vars, prec);
                double V_0 = 0.0;
                double V_t = 0.0;
                for(auto p : s) {
                    V_0 += log(std::max(prec, p.first));
                    V_t += log(std::max(prec, p.second));
                }
                return make_pair(V_0, V_t);
            };

            static unsigned counter = 0;

            while(ode_group_scores.size() > 0) {
                // update scores
                for(auto & t : ode_group_scores) {
                    unsigned i = get<0>(t);
                    // auto r = compute_max_width(diff_vec[i], _config.nra_precision);
                    auto r = compute_volume(diff_vec[i], _config.nra_precision);
                    t = make_pair(i, r);
                }
                // Sort
                std::sort(ode_group_scores.begin(), ode_group_scores.end(),
                          [&ratio_comp, &diff_comp](pair<unsigned, pair<double, double>> const & x,
                                        pair<unsigned, pair<double, double>> const & y) {
                              auto const & p1 = x.second;
                              auto const & p2 = y.second;
                              return !diff_comp(p1, p2);
                              // return false;
                          });

                // Process first n ode groups in parallel
                auto ite = ode_group_scores.begin();
                unsigned num_core = 1; // std::thread::hardware_concurrency()
                for(unsigned id = 0;
                    id < num_core && ite != ode_group_scores.end();
                    id++, ite++) {
                    auto t = *ite;
                    unsigned const i = t.first;
                    if(is_atomic(diff_vec[i], _config.nra_precision)) {
                        cerr << "A" << i << endl;
                        if (icp_solver::callODESolver(i, diff_vec[i], true) == false)
                            return false;
                    } else {
                        double const T_0_size = t.second.first;
                        double const T_x_size = t.second.second;
                        // if(T_x_size >= -4.0 && T_0_size >= -4.0) {
                        //     cerr << setw(20) << i << std::setw(20) << T_0_size << std::setw(20)
                        //          << T_x_size << std::setw(20) << "Skip" << endl;
                        // } else
                        if(T_x_size >= T_0_size) {
                            // cerr << "F" << i << " "p ;
                            cerr << setw(20) << i << std::setw(20) << T_0_size << std::setw(20)
                                 << T_x_size << std::setw(20) << "Forward" << endl;

                            if (icp_solver::callODESolver(i, diff_vec[i], true) == false) {
                                cerr << endl;
                                return false;
                            }
                        } else {
                            // cerr << "B" << i << " " ;
                            cerr << setw(20) << i <<std::setw(20) << T_0_size << std::setw(20)
                            << T_x_size << std::setw(20) << "Backward" << endl;
                            if (icp_solver::callODESolver(i, diff_vec[i], false) == false) {
                                cerr << endl;
                                return false;
                            }
                        }
                    }
                }
                // Delete first one
                ode_group_scores.erase(ode_group_scores.begin(), ite);
            }
            cerr << endl;
            counter++;
            // if(counter == ) {
            //     print_json(std::cerr);
            //     std::terminate();
            // }
            return true;
        } else {
            return true;
        }
    }
    return false;
}

// std::vector<std::thread> ts;
// #ifndef __APPLE__
// for (unsigned i = 0; i < 8; i++) {
//     ts.push_back(std::thread([&](){ mk(a); }));
// }
// for (unsigned i = 0; i < 8; i++) {
//     ts[i].join();
//     std::cout << "finished " << i << "\n";
// }

// //std::thread::hardware_concurrency();

//         // Parallel Version
//         boost::thread_group group;
//         unsigned hc = boost::thread::hardware_concurrency();
//         unsigned block = ceil(((double)max) / hc);
//         for(unsigned bn = 0; bn < block; bn++) {
//             for(unsigned i = 1; i <= hc && bn * hc + i <= max; i++) {
//                 group.create_thread(boost::bind(&icp_solver::callODESolver,
//                                                 this,
//                                                 bn * hc + i,
//                                                 diff_vec,
//                                                 current_box));
//             }
//             group.join_all();
//             if(!ODEresult) {
//                 return false;
//             }
//         }

// for (unsigned i = 1; i <= max; i++) {
//     if (!diff_vec[i].empty()) {
//         if (icp_solver::callODESolver(i, diff_vec[i]) == false)
//             return false;
//     }
// }

rp_box icp_solver::compute_next() {
    if (_sol > 0) {
        _boxes.remove();
    }
    while (!_boxes.empty()) {
        if (prop_with_ODE()) { // sean: here it is! propagation before split!!!
            int i = _vselect->apply(_boxes.get());
            if (i >= 0 && rp_box_width(_boxes.get()) >= _config.nra_precision) {
                if (_config.nra_proof) {
                    _config.nra_proof_out << endl
                                          << "[branched on "
                                          << rp_variable_name(rp_problem_var(*_problem, i))
                                          << "]"
                                          << endl;
                    pprint_vars(_config.nra_proof_out, *_problem, _boxes.get());
                }
                ++_nsplit;
                _dsplit->apply(_boxes, i);
            } else {
                ++_sol;
                if (_ep) _ep->prove(_boxes.get());
                return(_boxes.get());
            }
        } else {
            /* Added for dReal2 */
            if (_config.nra_proof) {
                _config.nra_proof_out << "[conflict detected]" << endl;
            }
            _boxes.remove();
        }
    }
    return nullptr;
}

void icp_solver::print_ODE_trajectory(ostream& out) const {
    if (ode_solvers.size() == 0)
        return;
    auto ite = ode_solvers.cbegin();
    (*ite++)->print_trajectory(out);
    while (ite != ode_solvers.cend()) {
        out << "," << endl;
        (*ite++)->print_trajectory(out);
    }
}

bool icp_solver::solve() {
    if (_config.nra_proof) {
        output_problem();
    }
    if (rp_box_empty(rp_problem_box(*_problem))) {
        if (_config.nra_verbose) {
            cerr << "Unfeasibility detected before solving";
        }
        /* TODO: currently, this is a naive explanation. */
        copy(m_stack.cbegin(), m_stack.cend(), back_inserter(_explanation));
        return false;
    } else {
        rp_box b;
        if ((b = compute_next()) != nullptr) {
            /* SAT */
            if (_config.nra_verbose) {
                cerr << "SAT with the following box:" << endl;
                pprint_vars(cerr, *_problem, b);
                cerr << endl;
            }
            if (_config.nra_proof) {
                _config.nra_proof_out << "SAT with the following box:" << endl;
                pprint_vars(_config.nra_proof_out, *_problem, b);
                _config.nra_proof_out << endl;
            }
            return true;
        } else {
            /* UNSAT */
            // _proof_out << "[conflict detected]" << endl;
            if (_config.nra_verbose) {
                cerr << "UNSAT!" << endl;
            }
            _explanation.clear();
            copy(m_stack.cbegin(), m_stack.cend(), back_inserter(_explanation));
            return false;
        }
    }
}

void icp_solver::display_box(ostream& out, rp_box b, int digits, int mode) const {
    if (rp_box_empty(b)) {
        out << "empty";
    } else {
        int i;
        out << "(";
        for (i = 0; i < rp_box_size(b); ++i) {
            // rp_interval_display(out,rp_box_elem(b,i),digits,mode);
            display_interval(out, rp_box_elem(b, i), digits, mode);
            if (i < (rp_box_size(b) - 1)) {
                out << ",";
            }
        }
        out << ")";
    }
}

void icp_solver::display_interval(ostream & out, rp_interval i, int digits, int mode) const {
    if (rp_interval_empty(i)) {
        out << "empty";
        return;
    }
    if (rp_interval_point(i)) {
        if (rp_binf(i) >= 0) {
// sprintf(out,"%.*g",digits,rp_binf(i));
            out.precision(digits);
            out << rp_binf(i);
        } else {
// sprintf(out,"%+.*g",digits,rp_binf(i));
            out.precision(digits);
            out << rp_binf(i);
        }
    } else {
        if (mode == RP_INTERVAL_MODE_BOUND) {
            if (rp_binf(i) >= 0) {
                if (rp_binf(i) == 0) {
                    // sprintf(out,"[0%s",RP_INTERVAL_SEPARATOR);
                    out << "[0" << RP_INTERVAL_SEPARATOR;
                } else {
                    RP_ROUND_DOWNWARD();
                    // sprintf(out,"[%.*g%s",digits,rp_binf(i),RP_INTERVAL_SEPARATOR);
                    out.precision(digits);
                    out << "[" << rp_binf(i) << RP_INTERVAL_SEPARATOR;
                }
                RP_ROUND_UPWARD();
                if (rp_bsup(i) == RP_INFINITY) {
                    // strcat(out,"+oo)");
                    out << "+oo";
                } else {
                    // char tmp[255];
                    // sprintf(tmp,"%.*g]",digits,rp_bsup(i));
                    // strcat(out,tmp);
                    out.precision(digits);
                    out << rp_bsup(i) << "]";
                }
            } else {
                RP_ROUND_DOWNWARD();
                if (rp_binf(i) == -RP_INFINITY) {
                    // sprintf(out,"(-oo%s",RP_INTERVAL_SEPARATOR);
                    out << "(-oo" << RP_INTERVAL_SEPARATOR;
                } else {
                    // sprintf(out,"[%+.*g%s",digits,rp_binf(i),RP_INTERVAL_SEPARATOR);
                    out.precision(digits);
                    out << "[" << rp_binf(i) << RP_INTERVAL_SEPARATOR;
                }
                RP_ROUND_UPWARD();
                if (rp_bsup(i) == RP_INFINITY) {
                    // strcat(out,"+oo)");
                    out << "+oo";
                } else {
                    if (rp_bsup(i) == 0) {
                        // strcat(out,"0]");
                        out << "0]";
                    } else {
                        // char tmp[255];
                        // sprintf(tmp,"%+.*g]",digits,rp_bsup(i));
                        // strcat(out,tmp);
                        out.precision(digits);
                        out << rp_bsup(i) << "]";
                    }
                }
            }
        }
    }
}

void icp_solver::pprint_vars(ostream & out, rp_problem p, rp_box b) const {
    for (int i = 0; i <rp_problem_nvar(p); i++) {
        out << setw(15);
        out << rp_variable_name(rp_problem_var(p, i));
        out << " : ";
        display_interval(out, rp_box_elem(b, i), 16, RP_INTERVAL_MODE_BOUND);
        if (i != rp_problem_nvar(p) - 1)
            out << ";";
        out << endl;
    }
}

void icp_solver::output_problem() const {
    _config.nra_proof_out.precision(16);
    _config.nra_proof_out << "Precision:" << _config.nra_precision << endl;

    // Print out all the Enode in stack
    for (auto ite = m_stack.cbegin(); ite != m_stack.cend(); ite++) {
        if ((*ite)->getPolarity() == l_True) {
            _config.nra_proof_out << *ite << endl;
        } else if ((*ite)->getPolarity() == l_False) {
            if ((*ite)->isEq()) {
                /* PRINT NOTHING */
            } else {
                _config.nra_proof_out << "(not " << *ite << ")" << endl;
            }
        } else {
            assert(0);
        }
    }

    // Print out the initial values
    for (auto ite = m_env.begin(); ite != m_env.end(); ite++) {
        Enode* key = (*ite).first;
        double lb = (*ite).second.first;
        double ub = (*ite).second.second;

        _config.nra_proof_out << key << ": ";
        if (lb == -numeric_limits<double>::infinity()) {
            _config.nra_proof_out << "(-oo";
        } else {
            _config.nra_proof_out.precision(16);
            _config.nra_proof_out << "[" << lb;
        }
        _config.nra_proof_out << ", ";
        if (ub == numeric_limits<double>::infinity()) {
            _config.nra_proof_out << "+oo)";
        } else {
            _config.nra_proof_out.precision(16);
            _config.nra_proof_out << ub << "]";
        }
        _config.nra_proof_out << ";" << endl;
    }
}


// return true if the box is non-empty after propagation
// false if the box is *empty* after propagation
bool icp_solver::prop() {
    bool result = false;
    if (_config.nra_proof) {
        output_problem();
    }
    if (_sol > 0) {
        _boxes.remove();
    }
    if (!_boxes.empty()) {
        result = _propag->apply(_boxes.get());
    }
    if (!result) {
        // UNSAT
        // Added for dReal2
        if (_config.nra_proof) {
            _config.nra_proof_out << "[conflict detected]" << endl;
        }
        // TODO(soonhok): better explanation
        _explanation.clear();
        copy(m_stack.cbegin(), m_stack.cend(), back_inserter(_explanation));
    } else {
        // SAT
        // Update Env
        // ======================================
        // Create rp_variable for each var in env
        // ======================================
        for (auto ite = m_env.begin(); ite != m_env.end(); ite++) {
            Enode* key = (*ite).first;
            // double lb = (*ite).second.first;
            // double ub = (*ite).second.second;
            int rp_id = _enode_to_rp_id[key];
            m_env.insert(key, make_pair(rp_binf(rp_box_elem(_boxes.get(), rp_id)),
                                       rp_bsup(rp_box_elem(_boxes.get(), rp_id))));
        }
        // cerr << "Incomplete Check: SAT" << endl;
        if (_config.nra_proof) {
            _config.nra_proof_out << "HOLE" << endl;
        }
    }
    return result;
}

void icp_solver::print_json(ostream & out) {
    // Print out ODE trajectory
    out << "{\"traces\": " << endl
        << "[" << endl;
    print_ODE_trajectory(out);
    out << "]" << endl;

    // collect all the ODE groups in the asserted literal and
    // print out
    set<int> ode_groups;
    for (auto lit = m_stack.cbegin(); lit != m_stack.cend(); lit++) {
        if ((*lit)->getPolarity() == l_True) {
            set<Enode*> const & variables_in_lit = _enode_to_vars[*lit];
            for (auto var = variables_in_lit.begin(); var != variables_in_lit.end(); var++) {
                if ((*var)->getODEvartype() == l_True) {
                    ode_groups.insert((*var)->getODEgroup());
                }
            }
        }
    }

    for (auto ite = m_env.begin(); ite != m_env.end(); ite++) {
        Enode* key = (*ite).first;
        double lb =  (*ite).second.first;
        double ub =  (*ite).second.second;
        if (starts_with(key->getCar()->getName(), "mode_")) {
            cerr << "Key: " << key << "\t Value: [" << lb << ", " << ub << "]" << endl;
        }
    }
    out << ", \"groups\": [";
    for (auto g = ode_groups.begin();
         g != ode_groups.end();
         g++) {
        if (g != ode_groups.begin()) {
            out << ", ";
        }
        out << *g;
    }
    out << "]" << endl << "}" << endl;
}
