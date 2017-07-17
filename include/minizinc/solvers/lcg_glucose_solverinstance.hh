/*
 *  Main authors:
 *     Kevin Leo <kevin.leo@monash.edu>
 *     Andrea Rendl <andrea.rendl@nicta.com.au>
 *     Guido Tack <guido.tack@monash.edu>
 */

/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */


#ifndef __MINIZINC_LCG_GLUCOSE_SOLVER_INSTANCE_HH__
#define __MINIZINC_LCG_GLUCOSE_SOLVER_INSTANCE_HH__

#include <minizinc/flattener.hh>
#include <minizinc/solver.hh>

#include <lcg_glucose/problem/lcg_glucose_problem.hh>

namespace MiniZinc {

  class LCGGlucoseSolverInstance : public SolverInstanceBase1 {   
  private:
#if 0
    bool _print_stats;
    bool _only_range_domains;
    bool _run_sac;
    bool _run_shave;
    unsigned int _pre_passes;
    bool _all_solutions;
    unsigned int _n_max_solutions;
    unsigned int _n_found_solutions;
#endif
    Model* _flat;
    Problem::LCGGlucoseProblem P;
    std::vector<OutputSpec> output_spec;
    int obj_type;
    Problem::Problem::IVar* obj_ivar;
  public:
    LCGGlucoseSolverInstance(Env& env, const Options& options);
    virtual ~LCGGlucoseSolverInstance(void);

    virtual Status next(void) { assert(0); return SolverInstance::UNKNOWN; }
    virtual void processFlatZinc(void);    
    virtual Status solve(void);
    virtual void resetSolver(void) { assert(0); }

    virtual Expression* getSolutionValue(Id* id);
  };
}

#endif
