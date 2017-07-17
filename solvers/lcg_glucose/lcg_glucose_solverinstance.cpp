/*
 *  Main authors:
 *     Kevin Leo <kevin.leo@monash.edu>
 *     Andrea Rendl <andrea.rendl@nicta.com.au>
 *     Guido Tack <guido.tack@monash.edu>
 *     Nick Downing <downing.nick@gmail.com>
 */

/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include <minizinc/exception.hh>
#include <minizinc/ast.hh>
#include <minizinc/eval_par.hh>

#include <lcg_glucose/utils/rassert.hpp>

#include <lcg_glucose/glucose/utils/System.h>
#include <lcg_glucose/glucose/utils/ParseUtils.h>
#include <lcg_glucose/glucose/utils/Options.h>

#include <lcg_glucose/problem/lcg_glucose_problem.hh>

#include <minizinc/solvers/lcg_glucose/fzn_solver.hpp>
#include <minizinc/solvers/lcg_glucose_solverinstance.hh>

using namespace std;

namespace MiniZinc {

  class LCGGlucose_SolverFactory: public SolverFactory {
    Options _options;
  public:
    SolverInstanceBase* doCreateSI(Env& env) {
      return new LCGGlucoseSolverInstance(env, _options);
    }
    string getVersion( );
    bool processOption(int& i, int argc, const char** argv);
    void printHelp(std::ostream& os);
  };
  
  SolverFactory* SolverFactory::createF_LCG_GLUCOSE() {
    return new LCGGlucose_SolverFactory;
  }

  string LCGGlucose_SolverFactory::getVersion()
  {
    string v = "LCG-glucose solver plugin, compiled  " __DATE__ "  " __TIME__;
    return v;
  }

  bool LCGGlucose_SolverFactory::processOption(int& i, int argc, const char** argv)
  {
#if 0
    if (string(argv[i])=="--only-range-domains") {
      _options.setBoolParam(std::string("only-range-domains"), true);
    } else if (string(argv[i])=="--sac") {
      _options.setBoolParam(std::string("sac"), true);
    } else if (string(argv[i])=="--shave") {
      _options.setBoolParam(std::string("shave"), true);
    } else if (string(argv[i])=="--pre-passes") {
      if (++i==argc) return false;
      int passes = atoi(argv[i]);
      if(passes >= 0)
        _options.setIntParam(std::string("pre_passes"), passes);
    } else
#endif
    if (string(argv[i])=="-a") {
      _options.setBoolParam(std::string("all_solutions"), true);
    }
#if 0
    else if (string(argv[i])=="-n") {
      if (++i==argc) return false;
      int n = atoi(argv[i]);
      if(n >= 0)
        _options.setIntParam(std::string("n_solutions"), n);
    } else if (string(argv[i])=="--node") {
      if (++i==argc) return false;
      int nodes = atoi(argv[i]);
      if(nodes >= 0)
        _options.setIntParam(std::string("nodes"), nodes);
    } else if (string(argv[i])=="--fail") {
      if (++i==argc) return false;
      int fails = atoi(argv[i]);
      if(fails >= 0)
        _options.setIntParam(std::string("fails"), fails);
    } else if (string(argv[i])=="--time") {
      if (++i==argc) return false;
      int time = atoi(argv[i]);
      if(time >= 0)
        _options.setIntParam(std::string("time"), time);
    }
#endif
    return true;
  }
  
  void LCGGlucose_SolverFactory::printHelp(ostream& os)
  {
    os
    << "LCG-glucose solver plugin options:" << std::endl
#if 0
    << "  --only-range-domains" << std::endl
    << "    only tighten bounds" << std::endl
    << "  --sac" << std ::endl
    << "    singleton arc consistency" << std::endl
    << "  --shave" << std::endl
    << "    shave domains" << std::endl
    << "  --pre-passes <n>" << std::endl
    << "    n passes of sac/shaving, 0 for fixed point" << std::endl
    << "  --node <n>" << std::endl
    << "    node cutoff (0 = none, solution mode)" << std::endl
    << "  --fail <f>" << std::endl
    << "    failure cutoff (0 = none, solution mode)" << std::endl
    << "  --time <ms>" << std::endl
    << "    time (in ms) cutoff (0 = none, solution mode)" << std::endl
#endif
    << "  -a" << std::endl
    << "    print intermediate solutions" << std::endl
#if 0
    << "  -n <sols>" << std::endl
    << "    number of solutions" << std::endl
#endif
    << std::endl;
  }

     LCGGlucoseSolverInstance::LCGGlucoseSolverInstance(Env& env, const Options& options)
       : SolverInstanceBase1(env,options),
       P(0, "% ", "% found solution objective "),
       obj_type(0),
       obj_ivar(0) {
       P.all_solutions = options.getBoolParam(std::string("all_solutions"), false);
       _flat = env.flat();
     }

    LCGGlucoseSolverInstance::~LCGGlucoseSolverInstance(void) {
      /*delete engine;*/
      //delete _current_space;
      // delete _solution; // TODO: is this necessary?
    }

  void LCGGlucoseSolverInstance::processFlatZinc(void) {
    static double initial_time = Glucose::cpuTime();
  
    {
      GCLock lock;
  
      Env env;
      try {
        XXXtypecheck_fzn(env, _flat);
      } catch (TypeError& e) {
        std::cerr << "Error: " << e.msg() << "\nIn file " << e.loc().filename.str() << ":" << e.loc().first_line << "c" << e.loc().first_column << "-" << e.loc().last_line << "c" << e.loc().last_column << std::endl;
        exit(EXIT_FAILURE);
      }

      EnterProblem ep(env.envi(), P, output_spec, obj_type, obj_ivar);
      iterItems<EnterProblem>(ep, _flat);
  
      GC::run();
    }
  
    if (obj_type) {
      std::pair<std::map<int, long long>, long long> res = obj_ivar->get_linear(obj_type);
      P.post_objective(obj_type, res.first, res.second);
    }
    else if (P.all_solutions) {
      for (int i = 0; i < output_spec.size(); ++i)
        for (int j = 0; j < output_spec[i].vars.size(); ++j)
          if (output_spec[i].ost == OST_BOOL)
            static_cast<Problem::Problem::BVar*>(output_spec[i].vars[j])->set_occurs(P);
          else
            static_cast<Problem::Problem::IVar*>(output_spec[i].vars[j])->set_occurs(P);
    }
    P.instantiate();
    P.gc();
  
    double parsed_time = Glucose::cpuTime();
    if (P.verbosity > 0)
      printf("%% Parse time      : %g s\n", parsed_time - initial_time);
  }

  Expression*
  LCGGlucoseSolverInstance::getSolutionValue(Id* id) {
    VarDecl* vd = id->decl();
    if (!id->type().isvar())
      return vd->e();
    rassert(vd->payload() > 0);
    Problem::Problem::Var *var = P.var[vd->payload() - 1];
    if (Problem::Problem::BVar *bvar = dynamic_cast<Problem::Problem::BVar *>(var))
      return new BoolLit(Location(), bvar->model_value(P));
    if (Problem::Problem::IVar *ivar = dynamic_cast<Problem::Problem::IVar *>(var))
      return IntLit::a(ivar->model_value(P));
    abort();
  }

struct XXXPrintSolData {
    std::vector<OutputSpec>& output_spec;
    std::vector<std::vector<long long> >& output_data;
    bool& output_data_valid;
    int obj_type;
    Problem::Problem::IVar* obj_ivar;
    SolverInstanceBase1& solver_instance;
    XXXPrintSolData(std::vector<OutputSpec>& output_spec0, std::vector<std::vector<long long> >& output_data0, bool& output_data_valid0, int obj_type0, Problem::Problem::IVar* obj_ivar0, SolverInstanceBase1& solver_instance0) :
        output_spec(output_spec0), output_data(output_data0), output_data_valid(output_data_valid0), obj_type(obj_type0), obj_ivar(obj_ivar0), solver_instance(solver_instance0) {}
};

static bool XXXprint_sol(Problem::Problem& P, void *data) {
    XXXPrintSolData& psd = *static_cast<XXXPrintSolData*>(data);
    GCLock lock;
    psd.solver_instance.assignSolutionToOutput();
    GC::run();
    psd.output_data_valid = true; /* actually no data unless all solutions */
    if (P.all_solutions) {
        psd.solver_instance.printSolution();
        if (psd.obj_type == 0) {
            psd.output_data.clear();
            for (int i = 0; i < static_cast<int>(psd.output_spec.size()); ++i)
                psd.output_data.push_back(psd.output_spec[i].model_values(P));

            std::vector<Problem::Problem::BVar*> t;
            for (int i = 0; i < static_cast<int>(psd.output_spec.size()); ++i)
                psd.output_spec[i].to_blocking_clause(P, psd.output_data[i], t);
            P.post_clause(t);
        }
        return true;
    }
    // not all solutions, only continue if optimization
    return psd.obj_type != 0; 
}

  SolverInstanceBase::Status
  LCGGlucoseSolverInstance::solve(void) {
    std::vector<std::vector<long long> > output_data;
    bool output_data_valid = false;
    XXXPrintSolData psd(output_spec, output_data, output_data_valid, obj_type, obj_ivar, *this);
    bool res = P.optimize(XXXprint_sol, &psd);
#if 0
// no need, because printSolution() always called later by our caller, it knows
// whether there is a solution pending from a previous assignSolutionToOutput()
    if (!P.all_solutions && output_data_valid)
      printSolution();
#endif
    return res ? output_data_valid ? SolverInstance::OPT : SolverInstance::UNSAT : output_data_valid ? SolverInstance::SAT : SolverInstance::UNKNOWN;
  }
};
