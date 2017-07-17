#ifndef _FZN_SOLVER_HPP
#define _FZN_SOLVER_HPP 1

#include <map>
#include <string>
#include <vector>

#include <minizinc/model.hh>
/*#include <minizinc/parser.hh>
#include <minizinc/typecheck.hh>
#include <minizinc/prettyprinter.hh>
#include <minizinc/exception.hh>
#include <minizinc/eval_par.hh>*/

#include <lcg_glucose/problem/problem.hh>

namespace MiniZinc {

enum OutputSpecType {OST_BOOL, OST_INT};
struct OutputSpec {
    OutputSpecType ost;
    std::string name;
    std::vector<std::pair<long long, long long> > dims;
    std::vector<Problem::Problem::Var*> vars;

    OutputSpec(OutputSpecType ost0, std::string name0, std::vector<std::pair<long long, long long> > dims0, std::vector<Problem::Problem::Var*> vars0);
    std::vector<long long> model_values(Problem::Problem& P);
    Expression* to_expression(long long data);
    AssignI* to_assign_item(std::vector<long long>& data);
    void to_blocking_clause(Problem::Problem& P, std::vector<long long>& data, std::vector<Problem::Problem::BVar*>& t);
};

class EnterProblem : public ItemVisitor {
public:
    EnvI& env;
    Problem::Problem& P;
    std::vector<OutputSpec>& output_spec;
    int& obj_type;
    Problem::Problem::IVar*& obj_ivar;
    std::vector<int> dependency_depth;

    static Problem::Problem::ConLevel get_con_level(Annotation& ann);
    static bool get_mdd_opts(Annotation& ann, Chuffed::MDDOpts& mdd_opts);
    Problem::Problem::Var* define_var(VarDecl* vd);
    Expression* get_const(Expression* e);
    long long get_bool(Expression* e);
    long long get_int(Expression* e);
    ASTExprVec<Expression> get_array(Expression* e);
    std::vector<long long> get_bool_array(Expression* e);
    std::vector<long long> get_int_array(Expression* e);
    std::vector<std::pair<long long, long long> > get_int_set(Expression* e);
    std::vector<std::vector<std::pair<long long, long long> > > get_int_set_array(Expression* e);
    std::pair<long long, long long> get_int_range(Expression* e);
    std::vector<std::pair<long long, long long> > get_int_range_array(Expression* e);
    double get_float(Expression* e);
    std::vector<double> get_float_array(Expression* e);
    Problem::Problem::BVar* get_bvar(Expression* e);
    Problem::Problem::IVar* get_ivar(Expression* e);
    std::vector<Problem::Problem::BVar*> get_bvar_array(Expression* e);
    std::vector<Problem::Problem::IVar*> get_ivar_array(Expression* e);
    std::vector<Problem::Problem::IVar*> get_ivar_pair(Expression* xe, Expression* ye);
    std::map<int, long long> get_ivar_terms(Expression* ae, Expression* xe);

    // these are only used with circulation and min_cost_flow and should not be 
    // confused with get_ivar_terms which is more useful, the subroutines below
    // are for extracting the meaning of a Boolean variable(s) from the model
    Problem::Problem::LinRel get_lin_rel(Expression* e);
    std::vector<Problem::Problem::LinRel> get_lin_rel_array(Expression* e);

    Problem::Problem::Search* get_search_spec(Expression* e);

    EnterProblem(EnvI& env0, Problem::Problem& P0, std::vector<OutputSpec>& output_spec0, int& obj_type0, Problem::Problem::IVar*& obj_ivar0);
    void vVarDeclI(VarDeclI* vdi);
    void vConstraintI(ConstraintI* ci);
    void vSolveI(SolveI* si);
};

#if 0 // this isn't necessary for the MZN solver, only the FZN solver
struct PrintSolData {
    std::vector<OutputSpec>& output_spec;
    std::vector<std::vector<long long> >& output_data;
    bool& output_data_valid;
    int obj_type;
    Problem::Problem::IVar* obj_ivar;
    PrintSolData(std::vector<OutputSpec>& output_spec0, std::vector<std::vector<long long> >& output_data0, bool& output_data_valid0, int obj_type0, Problem::Problem::IVar* obj_ivar0) :
        output_spec(output_spec0), output_data(output_data0), output_data_valid(output_data_valid0), obj_type(obj_type0), obj_ivar(obj_ivar0) {}
};
#endif

/*TEMP NORMALLY STATIC*/void XXXtypecheck_fzn(Env& env, Model* m);
/*TEMP NORMALLY STATIC*/bool print_sol(Problem::Problem& P, void *data);
void fzn_solver(Problem::Problem& P, std::string filename, int verbosity);

};

#endif 
