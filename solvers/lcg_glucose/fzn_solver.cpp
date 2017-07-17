#define DEFINE_VAR_USE_STACK 1
#define MAX_DEPENDENCY_DEPTH 100

#include <iostream>
#include <stdio.h> // phase this out, it's due to Glucose cruft
#include <stdlib.h>

#include <minizinc/astiterator.hh>
#include <minizinc/parser.hh>
#include <minizinc/typecheck.hh>
#include <minizinc/prettyprinter.hh>
#include <minizinc/eval_par.hh>

#include <lcg_glucose/utils/rassert.hpp>

#include <lcg_glucose/glucose/utils/System.h>
#include <lcg_glucose/glucose/utils/ParseUtils.h>
#include <lcg_glucose/glucose/utils/Options.h>

#include <minizinc/solvers/lcg_glucose/fzn_solver.hpp>

namespace MiniZinc {

OutputSpec::OutputSpec(OutputSpecType ost0, std::string name0, std::vector<std::pair<long long, long long> > dims0, std::vector<Problem::Problem::Var*> vars0) :
    ost(ost0), name(name0), dims(dims0), vars(vars0) {}

std::vector<long long> OutputSpec::model_values(Problem::Problem& P) {
    std::vector<long long> res;
    for (int i = 0; i < static_cast<int>(vars.size()); ++i)
 {
#if 0
  switch (ost) {
  case OST_BOOL: {
   Problem::Problem::BVar* bvar = static_cast<Problem::Problem::BVar*>(vars[i]);
   std::cerr << bvar->name << "=" << bvar->model_value(P);
   if (bvar->nbv2 >= 0)
std::cerr << " (nbv=" << P.model_value_nbv2(bvar->nbv2) << ")";
   std::cerr << "\n";
   break;
  }
  case OST_INT:
   Problem::Problem::IVar* ivar = static_cast<Problem::Problem::IVar*>(vars[i]);
   std::cerr << ivar->name << "=" << ivar->model_value(P);
   if (ivar->ibv2 >= 0)
    std::cerr << " (ibv=" << P.model_value_ibv2(ivar->ibv2) << ")";
   if (ivar->idv >= 0)
    std::cerr << " (idv=" << P.model_value_idv(ivar->idv) << ")";
   std::cerr << "\n";
   break;
  }
#endif
        res.push_back(ost == OST_BOOL ? static_cast<Problem::Problem::BVar*>(vars[i])->model_value(P) : static_cast<Problem::Problem::IVar*>(vars[i])->model_value(P));
 }
    return res;
}

Expression* OutputSpec::to_expression(long long data) {
    return ost == OST_BOOL ? static_cast<Expression*>(new BoolLit(Location(), data)) : static_cast<Expression*>(/*OLD MINIZINC new IntLit(Location(), data)*/ /*NEW MINIZINC*/IntLit::a(data));
}

AssignI* OutputSpec::to_assign_item(std::vector<long long>& data) {
    Expression* res;
    if (dims.empty())
        res = to_expression(data[0]);
    else {
        std::vector<Expression*> data1;
        for (int i = 0; i < static_cast<int>(data.size()); ++i)
            data1.push_back(to_expression(data[i]));
        std::vector<std::pair<int, int> > dims1;
        for (int i = 0; i < static_cast<int>(dims.size()); ++i)
            dims1.push_back(std::pair<int, int>(static_cast<int>(dims[i].first), static_cast<int>(dims[i].second)));
        res = new ArrayLit(Location(), data1, dims1);
    }
    return new AssignI(Location(), name, res);
}

void OutputSpec::to_blocking_clause(Problem::Problem& P, std::vector<long long>& data, std::vector<Problem::Problem::BVar*>& t) {
    for (int i = 0; i < vars.size(); ++i)
        if (ost == OST_BOOL) {
            Problem::Problem::BVar* x = static_cast<Problem::Problem::BVar*>(vars[i]);
            t.push_back(data[i] == 0 ? x : x->negate(P));
        }
        else {
            Problem::Problem::IVar* x = static_cast<Problem::Problem::IVar*>(vars[i]);
            if (x->has_idv())
                t.push_back(P.new_bvar_int_rel_reif(Problem::Problem::IRT_NE, x, P.new_ivar_const(data[i]), 0));
            else {
                t.push_back(P.new_bvar_int_rel_reif(Problem::Problem::IRT_LT, x, P.new_ivar_const(data[i]), 0));
                t.push_back(P.new_bvar_int_rel_reif(Problem::Problem::IRT_LT, P.new_ivar_const(data[i]), x, 0));
            }
        }
}

Problem::Problem::ConLevel EnterProblem::get_con_level(Annotation& ann) {
for (ExpressionSetIter p = ann.begin(); p != ann.end(); ++p)
    if (Id* id = (*p)->dyn_cast<Id>()) {
        if (id->str().str() == "bounds")
            return Problem::Problem::CL_BOUNDS;
        if (id->str().str() == "domain")
            return Problem::Problem::CL_DOMAIN;
    }
    return Problem::Problem::CL_VALUE;
}

bool EnterProblem::get_mdd_opts(Annotation& ann, Chuffed::MDDOpts& mdd_opts) {
    for (ExpressionSetIter p = ann.begin(); p != ann.end(); ++p) {
        Expression* e = *p;
        if (e->isa<Id>()) {
            if (e->cast<Id>()->str() == "mdd")
                return true;
        }
        else if (e->isa<Call>()) {
            Call* c = e->cast<Call>();
            if (c->id() == "mdd") {
                for (int i = 0; i < c->args().size(); ++i) {
                    rassert(c->args()[i]->isa<Id>());
                    mdd_opts.parse_arg(c->args()[i]->cast<Id>()->str().str());
                }
                return true;
            }
        }
    } 
    return false;
}

Problem::Problem::Var* EnterProblem::define_var(VarDecl* vd) {
 //std::cerr << "define_var " << *vd << " payload " << vd->payload() << "\n";
    Problem::Problem::Var* res;
    if (vd->payload() > 0)
        res = P.var[vd->payload() - 1];
    else if (vd->payload() < 0)
        res = 0; // due to re-entrancy **MAKE THIS SAFER, SEE int_lin_eq**
    else {
#if DEFINE_VAR_USE_STACK
        struct Stack {
            VarDecl* vd;
            int max_dependency_depth;
            int i;
            int j;
            Stack(VarDecl* vd0, int max_dependency_depth0, int i0, int j0) :
                vd(vd0), max_dependency_depth(max_dependency_depth0), i(i0), j(j0) {}
        };
        std::vector<Stack> stack;
#endif
        int max_dependency_depth;
        int i;
        int j;
        // temporaries which get reinstated after recursion:
        std::string name;
        ConstraintI* ci;
        Call* call;
        ASTExprVec<Expression> arg;
        VarDecl* vd1;
        // temporaries which get reinstated after recursion if array lit:
        ArrayLit* al;
        ASTExprVec<Expression> vec;
        // temporaries which do not need to be reinstated after recursion:
        Expression* e;
        Id* id1;
        ASTString id;
#if DEFINE_VAR_USE_STACK
    recurse:
#endif
        vd->payload(-1); // protect against re-entrancy
        max_dependency_depth = 0;
        rassert((vd->type().isbool() || vd->type().isint()) && !vd->ti()->isarray());
        name = vd->id()->str().str();
        ci = vd->defined_by();
        if (!ci)
            goto ordinary_var;
        rassert(!ci->removed());
        call = ci->e()->cast<Call>();
        arg = call->args();
        for (i = 0; i < arg.size(); ++i) {
            e = arg[i];
            while (id1 = e->dyn_cast<Id>()) {
                vd1 = id1->decl();
                assert(vd1);
                e = vd1->e();
                if (!e) {
                    if (vd1 != vd) {
                       if (vd1->payload() < 0) {
                            if (P.verbosity > 0)
                                std::cout << "% warning: breaking dependency on " << *arg[i] << " because circular: " << *call << "\n";
                            goto ordinary_var;
                        }
                        if (vd1->payload() == 0)
#if DEFINE_VAR_USE_STACK
                        {
                            stack.push_back(Stack(vd, max_dependency_depth, i, -1));
                            vd = vd1;
                            goto recurse;
                        resume_i:
                            ;
                        }
#else
                            define_var(vd1);
#endif
                        if (dependency_depth[vd1->payload() - 1] > max_dependency_depth) {
                            max_dependency_depth = dependency_depth[vd1->payload() - 1];
                            if (max_dependency_depth >= MAX_DEPENDENCY_DEPTH) {
                                if (P.verbosity > 0)
                                    std::cout << "% warning: breaking dependency on " << *arg[i] << " because too deep: " << *call << "\n";
                                goto ordinary_var;
                            }
                        }
                    }
                    goto continue_i;
                }
                // variable is just an alias for an expression, follow it
            }
            if ((al = e->dyn_cast<ArrayLit>()) != 0) {
                vec = al->v();
                for (j = 0; j < static_cast<int>(vec.size()); ++j) {
                    e = vec[j];
                    while (id1 = e->dyn_cast<Id>()) {
                        vd1 = id1->decl();
                        assert(vd1);
                        e = vd1->e();
                        if (!e) {
                            if (vd1 != vd) {
                                if (vd1->payload() < 0) {
                                    if (P.verbosity > 0)
                                        std::cout << "% warning: breaking dependency on " << *arg[i] << " because circular: " << *call << "\n";
                                    goto ordinary_var;
                                }
                                if (vd1->payload() == 0)
#if DEFINE_VAR_USE_STACK
                                {
                                    stack.push_back(Stack(vd, max_dependency_depth, i, j));
                                    vd = vd1;
                                    goto recurse;
                                resume_j:
                                    ;
                                }
#else
                                    define_var(vd1);
#endif
                                if (dependency_depth[vd1->payload() - 1] > max_dependency_depth) {
                                    max_dependency_depth = dependency_depth[vd1->payload() - 1];
                                    if (max_dependency_depth >= MAX_DEPENDENCY_DEPTH) {
                                        if (P.verbosity > 0)
                                            std::cout << "% warning: breaking dependency on " << *arg[i] << " because too deep: " << *call << "\n";
                                        goto ordinary_var;
                                    }
                                }
                            }
                            goto continue_j;
                        }
                        // variable is just an alias for an expression, follow it
                    }
                    if (e->dyn_cast<BoolLit>())
                        goto continue_j;
                    if (e->dyn_cast<IntLit>())
                        goto continue_j;
                    if (e->dyn_cast<FloatLit>())
                        goto continue_j;
                    if (e->dyn_cast<SetLit>())
                        goto continue_j;
                    std::cerr << "unsupported re-entrancy check expression in array literal: " << *e << "\n";
                    exit(EXIT_FAILURE);
                continue_j:
                    ;
                }
                goto continue_i;
            }
            if (e->dyn_cast<BoolLit>())
                goto continue_i;
            if (e->dyn_cast<IntLit>())
                goto continue_i;
            if (e->dyn_cast<FloatLit>())
                goto continue_i;
            if (e->dyn_cast<SetLit>())
                goto continue_i;
            std::cerr << "unsupported re-entrancy check expression: " << *e << "\n";
            exit(EXIT_FAILURE);
        continue_i:
            ;
        }
        id = call->id().str(); // name of defining constraint 
        if (vd->type().isbool()) {
            if (id == "set_in_reif")
                res = P.new_bvar_set_in_reif(name, get_ivar(arg[0]), get_int_set(arg[1]));
            else if (id == "array_bool_and")
                res = P.new_bvar_array_bool_and_or(name, Problem::Problem::AOT_AND, get_bvar_array(arg[0]));
            else if (id == "array_bool_or")
                res = P.new_bvar_array_bool_and_or(name, Problem::Problem::AOT_OR, get_bvar_array(arg[0]));
            else if (id == "bool_xor")
                res = P.new_bvar_bool_xor(name, get_bvar(arg[0]), get_bvar(arg[1]));
            else if (id == "all_different_int_reif")
                res = P.new_bvar_all_different_int_reif(name, get_ivar_array(arg[0]), get_con_level(call->ann()));
            else if (id == "int_element1d_reif")
                res = P.new_bvar_int_element1d_reif(name, get_int_range(arg[0]), get_int_array(arg[1]), get_ivar(arg[2]), get_ivar(arg[3]));
            else if (id == "int_element2d_reif")
                res = P.new_bvar_int_element2d_reif(name, get_int_range(arg[0]), get_int_range(arg[1]), get_int_array(arg[2]), get_ivar(arg[3]), get_ivar(arg[4]), get_ivar(arg[5]));
            else if (id == "bool_and_reif") {
                Problem::Problem::BVar* x = get_bvar(arg[0]);
                Problem::Problem::BVar* y = get_bvar(arg[1]);
                if (x->ub <= 0) // y & 0
                    res = P.new_bvar_const(0);
                else if (x->lb >= 1) // y & 1
                    res = y;
                else if (y->ub <= 0) // x & 0
                    res = P.new_bvar_const(0);
                else if (y->lb >= 1) // x & 1
                    res = x;
                else
                    res = P.new_bvar_bool_rel_reif(name, Problem::Problem::BRT_AND, x, y);
            }
            else if (id == "bool_or_reif") {
                Problem::Problem::BVar* x = get_bvar(arg[0]);
                Problem::Problem::BVar* y = get_bvar(arg[1]);
                if (x->ub <= 0) // y | 0
                    res = y;
                else if (x->lb >= 1) // y | 1
                    res = P.new_bvar_const(1);
                else if (y->ub <= 0) // x | 0
                    res = x;
                else if (y->lb >= 1) // x | 1
                    res = P.new_bvar_const(1);
                else
                    res = P.new_bvar_bool_rel_reif(name, Problem::Problem::BRT_OR, x, y);
            }
            else if (id == "bool_le_reif") {
                Problem::Problem::BVar* x = get_bvar(arg[0]);
                Problem::Problem::BVar* y = get_bvar(arg[1]);
                if (x->ub <= 0) // y >= 0
                    res = P.new_bvar_const(1);
                else if (x->lb >= 1) // y >= 1
                    res = y;
                else if (y->ub <= 0) // x <= 0
                    res = x->negate(P);
                else if (y->lb >= 1) // x <= 1
                    res = P.new_bvar_const(1);
                else
                    res = P.new_bvar_bool_rel_reif(name, Problem::Problem::BRT_LE, x, y);
            }
            else if (id == "bool_lt_reif") {
                Problem::Problem::BVar* x = get_bvar(arg[0]);
                Problem::Problem::BVar* y = get_bvar(arg[1]);
                if (x->ub <= 0) // y > 0
                    res = y;
                else if (x->lb >= 1) // y > 1
                    res = P.new_bvar_const(0);
                else if (y->ub <= 0) // x < 0
                    res = P.new_bvar_const(0);
                else if (y->lb >= 1) // x < 1
                    res = x->negate(P);
                else
                    res = P.new_bvar_bool_rel_reif(name, Problem::Problem::BRT_LT, x, y);
            }
            else if (id == "bool_eq_reif") {
                Problem::Problem::BVar* x = get_bvar(arg[0]);
                Problem::Problem::BVar* y = get_bvar(arg[1]);
                if (x->ub <= 0) // y = 0
                    res = y->negate(P);
                else if (x->lb >= 1) // y = 1
                    res = y;
                else if (y->ub <= 0) // x = 0
                    res = x->negate(P);
                else if (y->lb >= 1) // x = 1
                    res = x;
                else
                    res = P.new_bvar_bool_rel_reif(name, Problem::Problem::BRT_EQ, x, y);
            }
            else if (id == "bool_ne_reif") {
                Problem::Problem::BVar* x = get_bvar(arg[0]);
                Problem::Problem::BVar* y = get_bvar(arg[1]);
                if (x->ub <= 0) // y != 0
                    res = y;
                else if (x->lb >= 1) // y != 1
                    res = y->negate(P);
                else if (y->ub <= 0) // x != 0
                    res = x;
                else if (y->lb >= 1) // x != 1
                    res = x->negate(P);
                else
                    res = P.new_bvar_bool_rel_reif(name, Problem::Problem::BRT_NE, x, y);
            }
            else if (id == "int_le_reif")
                res = P.new_bvar_int_rel_reif(name, Problem::Problem::IRT_LE, get_ivar(arg[0]), get_ivar(arg[1]), 0);
            else if (id == "int_lt_reif")
                res = P.new_bvar_int_rel_reif(name, Problem::Problem::IRT_LT, get_ivar(arg[0]), get_ivar(arg[1]), 0);
            else if (id == "int_eq_reif")
                res = P.new_bvar_int_rel_reif(name, Problem::Problem::IRT_EQ, get_ivar(arg[0]), get_ivar(arg[1]), 0);
            else if (id == "int_ne_reif")
                res = P.new_bvar_int_rel_reif(name, Problem::Problem::IRT_NE, get_ivar(arg[0]), get_ivar(arg[1]), 0);
            else if (id == "int_lin_le_reif")
                res = P.new_bvar_int_lin_rel_reif(name, Problem::Problem::IRT_LE, get_ivar_terms(arg[0], arg[1]), get_int(arg[2]));
            else if (id == "int_lin_eq_reif")
                res = P.new_bvar_int_lin_rel_reif(name, Problem::Problem::IRT_EQ, get_ivar_terms(arg[0], arg[1]), get_int(arg[2]));
            else if (id == "int_lin_ne_reif")
                res = P.new_bvar_int_lin_rel_reif(name, Problem::Problem::IRT_NE, get_ivar_terms(arg[0], arg[1]), get_int(arg[2]));
            else if (id == "int_abs_reif")
                res = P.new_bvar_int_abs_reif(name, get_ivar(arg[0]), get_ivar(arg[1]));
            else if (id == "int_min_reif")
                res = P.new_bvar_array_int_min_max_reif(name, Problem::Problem::MMT_MIN, get_ivar(arg[2]), get_ivar_pair(arg[0], arg[1]));
            else if (id == "int_max_reif")
                res = P.new_bvar_array_int_min_max_reif(name, Problem::Problem::MMT_MAX, get_ivar(arg[2]), get_ivar_pair(arg[0], arg[1]));
            else if (id == "array_int_minimum_reif")
                res = P.new_bvar_array_int_min_max_reif(name, Problem::Problem::MMT_MIN, get_ivar(arg[0]), get_ivar_array(arg[1]));
            else if (id == "array_int_maximum_reif")
                res = P.new_bvar_array_int_min_max_reif(name, Problem::Problem::MMT_MAX, get_ivar(arg[0]), get_ivar_array(arg[1]));
            else if (id == "int_times_reif")
                res = P.new_bvar_int_times_reif(name, get_ivar(arg[0]), get_ivar(arg[1]), get_ivar(arg[2]));
            else if (id == "int_div_reif")
                res = P.new_bvar_int_div_reif(name, get_ivar(arg[0]), get_ivar(arg[1]), get_ivar(arg[2]));
            else if (id == "circulation_reif")
                res = P.new_bvar_circulation_reif(name, get_lin_rel_array(arg[0]));
            else if (id == "min_cost_flow_reif")
                res = P.new_bvar_min_cost_flow_reif(name, get_lin_rel(arg[0]), get_lin_rel_array(arg[1]));
            else if (id == "cumulative_reif")
                res = P.new_bvar_cumulative_reif(name, get_ivar_array(arg[0]), get_ivar_array(arg[1]), get_ivar_array(arg[2]), get_ivar(arg[3]));
            else if (id == "mdd") {
                Chuffed::MDDOpts mdd_opts;
                get_mdd_opts(call->ann(), mdd_opts);
                res = P.new_bvar_mdd_reif(name, get_ivar_array(arg[0]), get_int(arg[1]), get_int_array(arg[2]), get_int_array(arg[3]), mdd_opts);
            }
            else if (id == "cost_mdd") {
                Chuffed::MDDOpts mdd_opts;
                get_mdd_opts(call->ann(), mdd_opts);
                res = P.new_bvar_cost_mdd_reif(name, get_ivar_array(arg[0]), get_int(arg[1]), get_int_array(arg[2]), get_int_array(arg[3]), get_int_array(arg[4]), get_ivar(arg[5]), mdd_opts);
            }
            else if (id == "regular") {
                std::pair<bool, Chuffed::MDDOpts> mdd_opts;
                mdd_opts.first = get_mdd_opts(call->ann(), mdd_opts.second);
                res = P.new_bvar_regular_reif(name, get_ivar_array(arg[0]), get_int(arg[1]), get_int(arg[2]), get_int_array(arg[3]), get_int(arg[4]), get_int_set(arg[5]), mdd_opts);
            }
            else if (id == "cost_regular") {
                std::pair<bool, Chuffed::MDDOpts> mdd_opts;
                mdd_opts.first = get_mdd_opts(call->ann(), mdd_opts.second);
                res = P.new_bvar_cost_regular_reif(name, get_ivar_array(arg[0]), get_int(arg[1]), get_int(arg[2]), get_int_array(arg[3]), get_int_array(arg[4]), get_int(arg[5]), get_int_set(arg[6]), get_ivar(arg[7]), mdd_opts);
            }
            else {
                if (P.verbosity > 0)
                    std::cerr << "warning: unsupported bool defining constraint: " << *call << "\n";
                goto ordinary_var;
            }
        }
        else {
           if (id == "bool2int")
                res = P.new_ivar_bool2int_view(name, get_bvar(arg[0]));
            else if (id == "int_element1d")
                res = P.new_ivar_int_element1d(name, get_int_range(arg[0]), get_int_array(arg[1]), get_ivar(arg[2]));
            else if (id == "int_element2d")
                res = P.new_ivar_int_element2d(name, get_int_range(arg[0]), get_int_range(arg[1]), get_int_array(arg[2]), get_ivar(arg[3]), get_ivar(arg[4]));
            else if (id == "int_lin_eq") {
                ASTExprVec<Expression> a = get_array(arg[0]);
                ASTExprVec<Expression> x = get_array(arg[1]);
                rassert(a.size() == x.size());
                std::map<int, long long> t;
                long long c = get_int(arg[2]);
                long long sense = 0;
                for (int i = 0; i < static_cast<int>(a.size()); ++i) {
                    long long a1 = get_int(a[i]);
                    Problem::Problem::IVar* x1 = get_ivar(x[i]);
                    if (x1 == 0)
                        sense -= a1;
                    else if (x1->lb == x1->ub)
                        c -= a1 * x1->lb;
                    else
                        t[x1->var_no] += a1;
                }
                rassert(std::abs(sense) == 1);
                for (std::map<int, long long>::iterator p = t.begin(); p != t.end(); ++p)
                    p->second *= sense;
                c *= -sense;
                switch (t.size()) {
                case 0:
                    res = P.new_ivar_const(c);
                    break;
                case 1:
                    res = t.begin()->second == -1 && c == 0 ? static_cast<Problem::Problem::IVar*>(P.var[t.begin()->first])->negate(P) : P.new_ivar_affine_view(name, static_cast<Problem::Problem::IVar*>(P.var[t.begin()->first]), t.begin()->second, c);
                    break;
                default:
                    res = P.new_ivar_linear_view(name, t, c);
                    break;
                }
            }
            else if (id == "int_abs")
                res = P.new_ivar_int_abs(name, get_ivar(arg[0]));
            else if (id == "int_min")
                res = P.new_ivar_array_int_min_max(name, Problem::Problem::MMT_MIN, get_ivar_pair(arg[0], arg[1]));
            else if (id == "int_max")
                res = P.new_ivar_array_int_min_max(name, Problem::Problem::MMT_MAX, get_ivar_pair(arg[0], arg[1]));
            else if (id == "array_int_minimum")
                res = P.new_ivar_array_int_min_max(name, Problem::Problem::MMT_MIN, get_ivar_array(arg[1]));
            else if (id == "array_int_maximum")
                res = P.new_ivar_array_int_min_max(name, Problem::Problem::MMT_MAX, get_ivar_array(arg[1]));
            else if (id == "int_times")
                res = P.new_ivar_int_times(name, get_ivar(arg[0]), get_ivar(arg[1]));
            else if (id == "int_div")
                res = P.new_ivar_int_div(name, get_ivar(arg[0]), get_ivar(arg[1]));
            else {
                if (P.verbosity > 0)
                    std::cerr << "warning: unsupported int defining constraint: " << *call << "\n";
                goto ordinary_var;
            }
        }
        ci->remove();
        goto defined_var;
    ordinary_var:
        if (vd->type().isbool()) {
            rassert(!vd->ti()->domain());
 //std::cerr << "new_bvar " << name << "\n";
            res = P.new_bvar(name, 0, 1);
        }
        else {
            if (vd->ti()->domain() == 0) {
                std::cerr << "infinite domain not supported: " << *vd << "\n";
                    exit(EXIT_FAILURE);
            }
            IntSetVal* domain = eval_intset(env, vd->ti()->domain());
            rassert(domain->size());
 //std::cerr << "new_ivar " << name << " " << domain->min().toInt() << ".." << domain->max().toInt() << "\n";
            res = P.new_ivar(name, domain->min().toInt(), domain->max().toInt());
        }
    defined_var:
        vd->payload(res->var_no + 1);
        dependency_depth.resize(P.var.size(), 0);
        if (max_dependency_depth + 1 > dependency_depth[res->var_no])
            dependency_depth[res->var_no] = max_dependency_depth + 1;
#if DEFINE_VAR_USE_STACK
        if (!stack.empty()) {
            vd1 = vd;
            vd = stack.back().vd;
            max_dependency_depth = stack.back().max_dependency_depth;
            i = stack.back().i;
            j = stack.back().j;
            stack.pop_back();
            name = vd->id()->str().str();
            ci = vd->defined_by();
            assert(ci);
            call = ci->e()->cast<Call>();
            arg = call->args();
            if (j < 0)
                goto resume_i;
            e = arg[i];
            while (id1 = e->dyn_cast<Id>()) {
                VarDecl* vd1 = id1->decl();
                assert(vd1);
                e = vd1->e();
                assert(e);
                // variable is just an alias for an expression, follow it
            }
            assert(e->isa<ArrayLit>());
            al = e->cast<ArrayLit>();
            vec = al->v();
            goto resume_j;
        }
#endif
    }
 //std::cerr << "define_var done\n";
    return res;
}

Expression* EnterProblem::get_const(Expression* e) {
    while (Id* id = e->dyn_cast<Id>()) {
        VarDecl* vd = id->decl();
        assert(vd);
        e = vd->e();
        if (!e) {
            std::cerr << "unsupported const expression: " << *id << "\n";
            exit(EXIT_FAILURE);
        }
        // variable is just an alias for an expression, follow it
    }
    return e;
} 

long long EnterProblem::get_bool(Expression* e) {
    e = get_const(e);
    if (BoolLit* bl = e->dyn_cast<BoolLit>())
        return static_cast<long long>(bl->v());
    std::cerr << "unsupported bool expression: " << *e << "\n";
    exit(EXIT_FAILURE);
}

long long EnterProblem::get_int(Expression* e) {
    e = get_const(e);
    if (IntLit* il = e->dyn_cast<IntLit>())
        return il->v().toInt();
    std::cerr << "unsupported int expression: " << *e << "\n";
    exit(EXIT_FAILURE);
}

ASTExprVec<Expression> EnterProblem::get_array(Expression* e) {
    e = get_const(e);
    if (ArrayLit* al = e->dyn_cast<ArrayLit>())
        return al->v();
    std::cerr << "unsupported array expression: " << *e << "\n";
    exit(EXIT_FAILURE);
}

std::vector<long long> EnterProblem::get_bool_array(Expression* e) {
    ASTExprVec<Expression> vec = get_array(e);
    std::vector<long long> res;
    for (int i = 0; i < static_cast<int>(vec.size()); ++i)
        res.push_back(get_bool(vec[i]));
    return res;
}

std::vector<long long> EnterProblem::get_int_array(Expression* e) {
    ASTExprVec<Expression> vec = get_array(e);
    std::vector<long long> res;
    for (int i = 0; i < static_cast<int>(vec.size()); ++i)
        res.push_back(get_int(vec[i]));
    return res;
}

std::vector<std::pair<long long, long long> > EnterProblem::get_int_set(Expression* e) {
    e = get_const(e);
    if (SetLit* sl = e->dyn_cast<SetLit>()) {
        IntSetVal* set = eval_intset(env, sl);
        std::vector<std::pair<long long, long long> > res;
        for (int i = 0; i < static_cast<int>(set->size()); ++i)
            res.push_back(std::pair<long long, long long>(set->min(i).toInt(), set->max(i).toInt()));
        return res;
    }
    std::cerr << "unsupported int set expression: " << *e << "\n";
    exit(EXIT_FAILURE);
}

std::vector<std::vector<std::pair<long long, long long> > > EnterProblem::get_int_set_array(Expression* e) {
    ASTExprVec<Expression> vec = get_array(e);
    std::vector<std::vector<std::pair<long long, long long> > > res;
    for (int i = 0; i < static_cast<int>(vec.size()); ++i)
        res.push_back(get_int_set(vec[i]));
    return res;
}
 
std::pair<long long, long long> EnterProblem::get_int_range(Expression* e) {
    std::vector<std::pair<long long, long long> > res = get_int_set(e);
    if (res.size() == 0)
        return std::pair<long long, long long>(1, 0);
    if (res.size() == 1)
        return res[0];
    std::cerr << "unsupported int range expression: " << *e << "\n";
    exit(EXIT_FAILURE);
}

std::vector<std::pair<long long, long long> > EnterProblem::get_int_range_array(Expression* e) {
    ASTExprVec<Expression> vec = get_array(e);
    std::vector<std::pair<long long, long long> > res;
    for (int i = 0; i < static_cast<int>(vec.size()); ++i)
        res.push_back(get_int_range(vec[i]));
    return res;
}
 
double EnterProblem::get_float(Expression* e) {
    e = get_const(e);
    if (FloatLit* bl = e->dyn_cast<FloatLit>())
        return bl->v()/*NEW MINIZINC*/.toDouble();
    std::cerr << "unsupported float expression: " << *e << "\n";
    exit(EXIT_FAILURE);
}

std::vector<double> EnterProblem::get_float_array(Expression* e) {
    ASTExprVec<Expression> vec = get_array(e);
    std::vector<double> res;
    for (int i = 0; i < static_cast<int>(vec.size()); ++i)
        res.push_back(get_float(vec[i]));
    return res;
}

Problem::Problem::BVar* EnterProblem::get_bvar(Expression* e) {
    while (Id* id = e->dyn_cast<Id>()) {
        VarDecl* vd = id->decl();
        assert(vd);
        e = vd->e();
        if (!e) {
            Problem::Problem::Var* res = define_var(vd);
            rassert(!res || dynamic_cast<Problem::Problem::BVar*>(res));
            return static_cast<Problem::Problem::BVar*>(res);
        }
        // variable is just an alias for an expression, follow it
    }
    if (BoolLit* bl = e->dyn_cast<BoolLit>())
        return P.new_bvar_const(static_cast<long long>(bl->v()));
    std::cerr << "unsupported var bool expression: " << *e << "\n";
    exit(EXIT_FAILURE);
}

Problem::Problem::IVar* EnterProblem::get_ivar(Expression* e) {
    while (Id* id = e->dyn_cast<Id>()) {
        VarDecl* vd = id->decl();
        assert(vd);
        e = vd->e();
        if (!e) {
            Problem::Problem::Var* res = define_var(vd);
            rassert(!res || dynamic_cast<Problem::Problem::IVar*>(res));
            return static_cast<Problem::Problem::IVar*>(res);
        }
        // variable is just an alias for an expression, follow it
    }
    if (IntLit* il = e->dyn_cast<IntLit>())
        return P.new_ivar_const(il->v().toInt());
    std::cerr << "unsupported var int expression: " << *e << "\n";
    exit(EXIT_FAILURE);
}

std::vector<Problem::Problem::BVar*> EnterProblem::get_bvar_array(Expression* e) {
    ASTExprVec<Expression> vec = get_array(e);
    std::vector<Problem::Problem::BVar*> res;
    for (int i = 0; i < static_cast<int>(vec.size()); ++i)
        res.push_back(get_bvar(vec[i]));
    return res;
}

std::vector<Problem::Problem::IVar*> EnterProblem::get_ivar_array(Expression* e) {
    ASTExprVec<Expression> vec = get_array(e);
    std::vector<Problem::Problem::IVar*> res;
    for (int i = 0; i < static_cast<int>(vec.size()); ++i)
        res.push_back(get_ivar(vec[i]));
    return res;
}

std::vector<Problem::Problem::IVar*> EnterProblem::get_ivar_pair(Expression* xe, Expression* ye) {
    std::vector<Problem::Problem::IVar*> res;
    res.push_back(get_ivar(xe));
    res.push_back(get_ivar(ye));
    return res;
}
 
std::map<int, long long> EnterProblem::get_ivar_terms(Expression* ae, Expression* xe) {
    ASTExprVec<Expression> a = get_array(ae);
    ASTExprVec<Expression> x = get_array(xe);
    rassert(a.size() == x.size());
    std::map<int, long long> t;
    for (int i = 0; i < static_cast<int>(a.size()); ++i)
        t[get_ivar(x[i])->var_no] += get_int(a[i]);
    return t;
}

// these are only used with circulation and min_cost_flow and should not be 
// confused with get_ivar_terms which is more useful, the subroutines below
// are for extracting the meaning of a Boolean variable(s) from the model
Problem::Problem::LinRel EnterProblem::get_lin_rel(Expression* e) {
    return get_bvar(e)->get_lin_rel(P);
}

std::vector<Problem::Problem::LinRel> EnterProblem::get_lin_rel_array(Expression* e) {
    ASTExprVec<Expression> vec = get_array(e);
    std::vector<Problem::Problem::LinRel> res;
    for (int i = 0; i < static_cast<int>(vec.size()); ++i)
        res.push_back(get_lin_rel(vec[i]));
    return res;
}

Problem::Problem::Search* EnterProblem::get_search_spec(Expression* e) {
    if (Call* call = e->dyn_cast<Call>()) {
        ASTString id = call->id().str();
        ASTExprVec<Expression> arg = call->args();
        Problem::Problem::Search* res;
        if (id == "seq_search") {
            ASTExprVec<Expression> vec = get_array(arg[0]);
            std::vector<Problem::Problem::Search*> x;
            for (int i = 0; i < static_cast<int>(vec.size()); ++i)
                x.push_back(get_search_spec(vec[i]));
            res = P.new_seq_search(x);
        }
        else if (id == "bool_search") {
            Problem::Problem::BoolSearchVarSelType bsrst;
            if (Id* id1 = arg[1]->dyn_cast<Id>()) {
                if (id1->str() == "input_order")
                    bsrst = Problem::Problem::BSRST_INPUT_ORDER;
                else if (id1->str() == "activity")
                    bsrst = Problem::Problem::BSRST_ACTIVITY;
                else {
                    std::cerr << "unsupported bool_search variable selection annotation: " << *id1 << "\n";
                    exit(EXIT_FAILURE);
                }
            }
            else {
                std::cerr << "unsupported bool_search variable selection expression: " << *arg[1] << "\n";
                exit(EXIT_FAILURE);
            }
            Problem::Problem::BoolSearchValSelType bslst;
            if (Id* id1 = arg[2]->dyn_cast<Id>()) {
                if (id1->str() == "indomain_min" || id1->str() == "indomain")
                    bslst = Problem::Problem::BSLST_INDOMAIN_MIN;
                else if (id1->str() == "indomain_max")
                    bslst = Problem::Problem::BSLST_INDOMAIN_MAX;
                else if (id1->str() == "circulation_split")
                    bslst = Problem::Problem::BSLST_CIRCULATION_SPLIT;
                else if (id1->str() == "min_cost_flow_split")
                    bslst = Problem::Problem::BSLST_MIN_COST_FLOW_SPLIT;
                else {
                    std::cerr << "unsupported bool_search value selection annotation: " << *id1 << "\n";
                    exit(EXIT_FAILURE);
                }
            }
            else {
                std::cerr << "unsupported bool_search variable selection expression: " << *arg[2] << "\n";
                exit(EXIT_FAILURE);
            }
            res = P.new_bool_search(get_bvar_array(arg[0]), bsrst, bslst);
        }
        else if (id == "int_search") {
            Problem::Problem::IntSearchVarSelType isrst;
            if (Id* id1 = arg[1]->dyn_cast<Id>()) {
                if (id1->str() == "input_order")
                    isrst = Problem::Problem::ISRST_INPUT_ORDER;
                else if (id1->str() == "first_fail")
                    isrst = Problem::Problem::ISRST_FIRST_FAIL;
                else if (id1->str() == "anti_first_fail")
                    isrst = Problem::Problem::ISRST_ANTI_FIRST_FAIL;
                else if (id1->str() == "smallest")
                    isrst = Problem::Problem::ISRST_SMALLEST;
                else if (id1->str() == "largest")
                    isrst = Problem::Problem::ISRST_LARGEST;
                else if (id1->str() == "activity")
                    isrst = Problem::Problem::ISRST_ACTIVITY;
                else {
                    std::cerr << "unsupported int_search variable selection annotation: " << *id1 << "\n";
                    exit(EXIT_FAILURE);
                }
            }
            else {
                std::cerr << "unsupported int_search variable selection expression: " << *arg[1] << "\n";
                exit(EXIT_FAILURE);
            }
            Problem::Problem::IntSearchValSelType islst;
            if (Id* id1 = arg[2]->dyn_cast<Id>()) {
                if (id1->str() == "indomain_min" || id1->str() == "indomain")
                    islst = Problem::Problem::ISLST_INDOMAIN_MIN;
                else if (id1->str() == "indomain_max")
                    islst = Problem::Problem::ISLST_INDOMAIN_MAX;
                else if (id1->str() == "indomain_median")
                    islst = Problem::Problem::ISLST_INDOMAIN_MEDIAN;
                else if (id1->str() == "indomain_split")
                    islst = Problem::Problem::ISLST_INDOMAIN_SPLIT;
                else if (id1->str() == "indomain_reverse_split")
                    islst = Problem::Problem::ISLST_INDOMAIN_REVERSE_SPLIT;
                else if (id1->str() == "circulation_split")
                    islst = Problem::Problem::ISLST_CIRCULATION_SPLIT;
                else if (id1->str() == "min_cost_flow_split")
                    islst = Problem::Problem::ISLST_MIN_COST_FLOW_SPLIT;
                else {
                    std::cerr << "unsupported int_search value selection annotation: " << *id1 << "\n";
                    exit(EXIT_FAILURE);
                }
            }
            else {
                std::cerr << "unsupported int_search variable selection expression: " << *arg[2] << "\n";
                exit(EXIT_FAILURE);
            }
            res = P.new_int_search(get_ivar_array(arg[0]), isrst, islst);
        }
        else {
            std::cerr << "unsupported search specification annotation: " << *call << "\n";
            exit(EXIT_FAILURE);
        }
        return res;
    }
    else {
        std::cerr << "unsupported search specification expression: " << *e << "\n";
        exit(EXIT_FAILURE);
    } 
}

EnterProblem::EnterProblem(EnvI& env0, Problem::Problem& P0, std::vector<OutputSpec>& output_spec0, int& obj_type0, Problem::Problem::IVar*& obj_ivar0) :
    env(env0), P(P0), output_spec(output_spec0), obj_type(obj_type0), obj_ivar(obj_ivar0) {}

// paranoidly intersect domains of overlapping declarations
void EnterProblem::vVarDeclI(VarDeclI* vdi) {
    VarDecl* vd = vdi->e()->cast<VarDecl>();
 //std::cerr << "vVarDeclI " << *vd << "\n";
    if (vd->ti()->isarray()) {
        rassert(vd->e());
        if (vd->ti()->type().isint() && vd->ti()->domain()) {
            std::vector<std::pair<long long, long long> > domain = get_int_set(vd->ti()->domain());
            rassert(!domain.empty());
            std::vector<Problem::Problem::IVar*> vec = get_ivar_array(vd->e());
            for (int i = 0; i < static_cast<int>(vec.size()); ++i) {
                if (domain[0].first > vec[i]->lb)
                    vec[i]->incr_lb(P, domain[0].first);
                if (domain.back().second < vec[i]->ub)
                    vec[i]->decr_ub(P, domain.back().second);
                if (domain.size() > 1)
                    P.post_set_in_halfreif(vec[i], domain, P.new_bvar_const(1));
            }
        }
        for (ExpressionSetIter p = vd->ann().begin(); p != vd->ann().end(); ++p)
            if (Call* call = (*p)->dyn_cast<Call>())
                if (call->id().str() == "output_array") {
                    OutputSpecType ost;
                    std::vector<Problem::Problem::Var*> vars;
                    if (vd->ti()->type().isboolarray()) {
                        ost = OST_BOOL;
                        std::vector<Problem::Problem::BVar*> bvars = get_bvar_array(vd->e());
                        for (int i = 0; i < bvars.size(); ++i)
                            vars.push_back(bvars[i]);
                    }
                    else if (vd->ti()->type().isintarray()) {
                        ost = OST_INT;
                        std::vector<Problem::Problem::IVar*> ivars = get_ivar_array(vd->e());
                        for (int i = 0; i < ivars.size(); ++i)
                            vars.push_back(ivars[i]);
                    }
                    else {
                        std::cerr << "unsupported output_array: " << *vd << "\n";
                        exit(EXIT_FAILURE);
                    }
                    output_spec.push_back(OutputSpec(ost, vd->id()->str().str(), get_int_range_array(call->args()[0]), vars));
                }
    }
    else if (vd->ti()->type().isbool()) {
        Problem::Problem::BVar* var = vd->e() ? get_bvar(vd->e()) : static_cast<Problem::Problem::BVar*>(define_var(vd));
        for (ExpressionSetIter p = vd->ann().begin(); p != vd->ann().end(); ++p)
            if (Id* id = (*p)->dyn_cast<Id>())
                if (id->str().str() == "output_var") {
                    std::vector<Problem::Problem::Var*> vars;
                    vars.push_back(var);
                    output_spec.push_back(OutputSpec(OST_BOOL, vd->id()->str().str(), std::vector<std::pair<long long, long long> >(), vars));
                }
    }
    else if (vd->ti()->type().isint()) {
        Problem::Problem::IVar* var = vd->e() ? get_ivar(vd->e()) : static_cast<Problem::Problem::IVar*>(define_var(vd));
        if (vd->ti()->domain()) {
            std::vector<std::pair<long long, long long> > domain = get_int_set(vd->ti()->domain());
            rassert(!domain.empty());
            if (domain[0].first > var->lb)
                var->incr_lb(P, domain[0].first);
            if (domain.back().second < var->ub)
                var->decr_ub(P, domain.back().second);
            if (domain.size() > 1)
 //{
 // std::cerr << "a " << var->name << " in";
 // for (int i = 0; i < domain.size(); ++i)
 //  std::cerr << " " << domain[i].first << "," << domain[i].second;
 // std::cerr << "\n";
                P.post_set_in_halfreif(var, domain, P.new_bvar_const(1));
 //}
        }
        for (ExpressionSetIter p = vd->ann().begin(); p != vd->ann().end(); ++p)
            if (Id* id = (*p)->dyn_cast<Id>())
                if (id->str().str() == "output_var") {
                    std::vector<Problem::Problem::Var*> vars;
                    vars.push_back(var);
                    output_spec.push_back(OutputSpec(OST_INT, vd->id()->str().str(), std::vector<std::pair<long long, long long> >(), vars));
                }
    } 
    else {
        std::cerr << "unsupported variable type: " << *vd << "\n"; 
        exit(EXIT_FAILURE);
    }
}

void EnterProblem::vConstraintI(ConstraintI* ci) {
 //std::cerr << "vConstraintI " << *ci << "\n";
    if (Call* call = ci->e()->dyn_cast<Call>()) {
#if 0 // doesn't work if cycles have to be broken
 for (ExpressionSetIter p = call->ann().begin(); p != call->ann().end(); ++p)
  if (Call* call1 = (*p)->dyn_cast<Call>()) {
   if (call1->id().str() == "defines_var") {
if (Id* id = call1->args()[0]->dyn_cast<Id>()) {
 if (id->decl()->defined_by()->e() == call)
  abort(); //return;
}
   }
  }
#endif
        ASTString id = call->id().str();
        ASTExprVec<Expression> arg = call->args();
        if (id == "bool2int")
            P.post_bool2int(get_bvar(arg[0]), get_ivar(arg[1]));
        else if (id == "set_in")
            P.post_set_in_halfreif(get_ivar(arg[0]), get_int_set(arg[1]), P.new_bvar_const(1));
        else if (id == "set_in_reif")
            P.post_set_in_reif(get_ivar(arg[0]), get_int_set(arg[1]), get_bvar(arg[2]));
        else if (id == "array_bool_and")
            P.post_array_bool_and_or_halfreif(Problem::Problem::AOT_AND, get_bvar_array(arg[0]), get_bvar(arg[1]), P.new_bvar_const(1));
        else if (id == "array_bool_or")
            P.post_array_bool_and_or_halfreif(Problem::Problem::AOT_OR, get_bvar_array(arg[0]), get_bvar(arg[1]), P.new_bvar_const(1));
        else if (id == "bool_xor")
            P.post_bool_xor_halfreif(get_bvar(arg[0]), get_bvar(arg[1]), get_bvar(arg[2]), P.new_bvar_const(1));
        else if (id == "bool_clause") {
            std::vector<Problem::Problem::BVar*> x = get_bvar_array(arg[0]);
            std::vector<Problem::Problem::BVar*> y = get_bvar_array(arg[1]);
            for (int i = 0; i < static_cast<int>(y.size()); ++i)
                x.push_back(y[i]->negate(P));
            P.post_clause(x);
        }
        else if (id == "all_different_int")
            P.post_all_different_int_halfreif(get_ivar_array(arg[0]), P.new_bvar_const(1), get_con_level(call->ann()));
        else if (id == "int_element1d")
            P.post_int_element1d_halfreif(get_int_range(arg[0]), get_int_array(arg[1]), get_ivar(arg[2]), get_ivar(arg[3]), P.new_bvar_const(1));
        else if (id == "int_element2d")
            P.post_int_element2d_halfreif(get_int_range(arg[0]), get_int_range(arg[1]), get_int_array(arg[2]), get_ivar(arg[3]), get_ivar(arg[4]), get_ivar(arg[5]), P.new_bvar_const(1));
        else if (id == "bool_and")
            P.post_bool_rel_reif(Problem::Problem::BRT_AND, get_bvar(arg[0]), get_bvar(arg[1]), P.new_bvar_const(1));
        else if (id == "bool_and_reif")
            P.post_bool_rel_reif(Problem::Problem::BRT_AND, get_bvar(arg[0]), get_bvar(arg[1]), get_bvar(arg[2]));
        else if (id == "bool_or")
            P.post_bool_rel_reif(Problem::Problem::BRT_OR, get_bvar(arg[0]), get_bvar(arg[1]), P.new_bvar_const(1));
        else if (id == "bool_or_reif")
            P.post_bool_rel_reif(Problem::Problem::BRT_OR, get_bvar(arg[0]), get_bvar(arg[1]), get_bvar(arg[2]));
        else if (id == "bool_le")
            P.post_bool_rel_reif(Problem::Problem::BRT_LE, get_bvar(arg[0]), get_bvar(arg[1]), P.new_bvar_const(1));
        else if (id == "bool_le_reif")
            P.post_bool_rel_reif(Problem::Problem::BRT_LE, get_bvar(arg[0]), get_bvar(arg[1]), get_bvar(arg[2]));
        else if (id == "bool_lt")
            P.post_bool_rel_reif(Problem::Problem::BRT_LT, get_bvar(arg[0]), get_bvar(arg[1]), P.new_bvar_const(1));
        else if (id == "bool_lt_reif")
            P.post_bool_rel_reif(Problem::Problem::BRT_LT, get_bvar(arg[0]), get_bvar(arg[1]), get_bvar(arg[2]));
        else if (id == "bool_eq")
            P.post_bool_rel_reif(Problem::Problem::BRT_EQ, get_bvar(arg[0]), get_bvar(arg[1]), P.new_bvar_const(1));
        else if (id == "bool_eq_reif")
            P.post_bool_rel_reif(Problem::Problem::BRT_EQ, get_bvar(arg[0]), get_bvar(arg[1]), get_bvar(arg[2]));
        else if (id == "bool_ne")
            P.post_bool_rel_reif(Problem::Problem::BRT_NE, get_bvar(arg[0]), get_bvar(arg[1]), P.new_bvar_const(1));
        else if (id == "bool_ne_reif")
            P.post_bool_rel_reif(Problem::Problem::BRT_NE, get_bvar(arg[0]), get_bvar(arg[1]), get_bvar(arg[2]));
        else if (id == "int_le")
            P.post_int_rel_reif(Problem::Problem::IRT_LE, get_ivar(arg[0]), get_ivar(arg[1]), 0, P.new_bvar_const(1));
        else if (id == "int_le_reif")
            P.post_int_rel_reif(Problem::Problem::IRT_LE, get_ivar(arg[0]), get_ivar(arg[1]), 0, get_bvar(arg[2]));
        else if (id == "int_lt")
            P.post_int_rel_reif(Problem::Problem::IRT_LT, get_ivar(arg[0]), get_ivar(arg[1]), 0, P.new_bvar_const(1));
        else if (id == "int_lt_reif")
            P.post_int_rel_reif(Problem::Problem::IRT_LT, get_ivar(arg[0]), get_ivar(arg[1]), 0, get_bvar(arg[2]));
        else if (id == "int_eq")
            P.post_int_rel_reif(Problem::Problem::IRT_EQ, get_ivar(arg[0]), get_ivar(arg[1]), 0, P.new_bvar_const(1));
        else if (id == "int_eq_reif")
 //{
 // std::cerr << "a " << *arg[0] << " " << *arg[1] << " " << *arg[2] << "\n";
            P.post_int_rel_reif(Problem::Problem::IRT_EQ, get_ivar(arg[0]), get_ivar(arg[1]), 0, get_bvar(arg[2]));
 //}
        else if (id == "int_ne")
            P.post_int_rel_reif(Problem::Problem::IRT_NE, get_ivar(arg[0]), get_ivar(arg[1]), 0, P.new_bvar_const(1));
        else if (id == "int_ne_reif")
            P.post_int_rel_reif(Problem::Problem::IRT_NE, get_ivar(arg[0]), get_ivar(arg[1]), 0, get_bvar(arg[2]));
        else if (id == "int_lin_le")
            P.post_int_lin_rel_reif(Problem::Problem::IRT_LE, get_ivar_terms(arg[0], arg[1]), get_int(arg[2]), P.new_bvar_const(1));
        else if (id == "int_lin_le_reif")
            P.post_int_lin_rel_reif(Problem::Problem::IRT_LE, get_ivar_terms(arg[0], arg[1]), get_int(arg[2]), get_bvar(arg[3]));
        else if (id == "int_lin_eq")
            P.post_int_lin_rel_reif(Problem::Problem::IRT_EQ, get_ivar_terms(arg[0], arg[1]), get_int(arg[2]), P.new_bvar_const(1));
        else if (id == "int_lin_eq_reif")
            P.post_int_lin_rel_reif(Problem::Problem::IRT_EQ, get_ivar_terms(arg[0], arg[1]), get_int(arg[2]), get_bvar(arg[3]));
        else if (id == "int_lin_ne")
            P.post_int_lin_rel_reif(Problem::Problem::IRT_NE, get_ivar_terms(arg[0], arg[1]), get_int(arg[2]), P.new_bvar_const(1));
        else if (id == "int_lin_ne_reif")
            P.post_int_lin_rel_reif(Problem::Problem::IRT_NE, get_ivar_terms(arg[0], arg[1]), get_int(arg[2]), get_bvar(arg[3]));
        else if (id == "int_abs")
            P.post_int_abs_halfreif(get_ivar(arg[0]), get_ivar(arg[1]), P.new_bvar_const(1));
        else if (id == "int_min")
            P.post_array_int_min_max_halfreif(Problem::Problem::MMT_MIN, get_ivar(arg[2]), get_ivar_pair(arg[0], arg[1]), P.new_bvar_const(1));
        else if (id == "int_max")
            P.post_array_int_min_max_halfreif(Problem::Problem::MMT_MAX, get_ivar(arg[2]), get_ivar_pair(arg[0], arg[1]), P.new_bvar_const(1));
        else if (id == "array_int_minimum")
            P.post_array_int_min_max_halfreif(Problem::Problem::MMT_MIN, get_ivar(arg[0]), get_ivar_array(arg[1]), P.new_bvar_const(1));
        else if (id == "array_int_maximum")
            P.post_array_int_min_max_halfreif(Problem::Problem::MMT_MAX, get_ivar(arg[0]), get_ivar_array(arg[1]), P.new_bvar_const(1));
        else if (id == "int_times")
            P.post_int_times_halfreif(get_ivar(arg[0]), get_ivar(arg[1]), get_ivar(arg[2]), P.new_bvar_const(1));
        else if (id == "int_div")
            P.post_int_div_halfreif(get_ivar(arg[0]), get_ivar(arg[1]), get_ivar(arg[2]), P.new_bvar_const(1));
        else if (id == "circulation")
            P.post_circulation_halfreif(get_lin_rel_array(arg[0]), P.new_bvar_const(1));
        else if (id == "min_cost_flow")
            P.post_min_cost_flow_halfreif(get_lin_rel(arg[0]), get_lin_rel_array(arg[1]), P.new_bvar_const(1));
        else if (id == "cumulative")
            P.post_cumulative_halfreif(get_ivar_array(arg[0]), get_ivar_array(arg[1]), get_ivar_array(arg[2]), get_ivar(arg[3]), P.new_bvar_const(1));
        else if (id == "mdd") {
            Chuffed::MDDOpts mdd_opts;
            get_mdd_opts(call->ann(), mdd_opts);
            P.post_mdd_halfreif(get_ivar_array(arg[0]), get_int(arg[1]), get_int_array(arg[2]), get_int_array(arg[3]), P.new_bvar_const(1), mdd_opts);
        }
        else if (id == "cost_mdd") {
            Chuffed::MDDOpts mdd_opts;
            get_mdd_opts(call->ann(), mdd_opts);
            P.post_cost_mdd_halfreif(get_ivar_array(arg[0]), get_int(arg[1]), get_int_array(arg[2]), get_int_array(arg[3]), get_int_array(arg[4]), get_ivar(arg[5]), P.new_bvar_const(1), mdd_opts);
        }
        else if (id == "regular") {
            std::pair<bool, Chuffed::MDDOpts> mdd_opts;
            mdd_opts.first = get_mdd_opts(call->ann(), mdd_opts.second);
            P.post_regular_halfreif(get_ivar_array(arg[0]), get_int(arg[1]), get_int(arg[2]), get_int_array(arg[3]), get_int(arg[4]), get_int_set(arg[5]), P.new_bvar_const(1), mdd_opts);
        }
        else if (id == "cost_regular") {
            std::pair<bool, Chuffed::MDDOpts> mdd_opts;
            mdd_opts.first = get_mdd_opts(call->ann(), mdd_opts.second);
            P.post_cost_regular_halfreif(get_ivar_array(arg[0]), get_int(arg[1]), get_int(arg[2]), get_int_array(arg[3]), get_int_array(arg[4]), get_int(arg[5]), get_int_set(arg[6]), get_ivar(arg[7]), P.new_bvar_const(1), mdd_opts);
        }
        else {
            std::cerr << "unsupported constraint call: " << *call << "\n";
            exit(EXIT_FAILURE);
        }
    }
    else {
        std::cerr << "unsupported constraint expression: " << *ci->e() << "\n";
        exit(EXIT_FAILURE);
    } 
}

void EnterProblem::vSolveI(SolveI* si) {
    if (!P.free_search) {
        std::vector<Problem::Problem::Search*> x;
        for (ExpressionSetIter p = si->ann().begin(); p != si->ann().end(); ++p) {
            if (Call* call = (*p)->dyn_cast<Call>()) {
                ASTString id = call->id().str();
                ASTExprVec<Expression> arg = call->args();
                if (id == "restart") {
                    P.post_restart_spec(static_cast<int>(get_int(arg[0])), static_cast<int>(get_int(arg[1])), get_float(arg[2]));
                    continue;
                }
            }
            x.push_back(get_search_spec(*p));
        }
        if (!x.empty()) {
            P.post_search_spec(x.size() == 1 ? x[0] : P.new_seq_search(x));
            if (!P.has_restart_spec())
                P.post_restart_spec(0);
        }
    }
    if (si->e()) {
        switch (si->st()) {
        case SolveI::ST_MIN:
            obj_type = 1;
            break;
        case SolveI::ST_MAX:
            obj_type = -1;
            break;
        default:
            abort();
        }
        obj_ivar = get_ivar(si->e());
    }
}

/*static*/ void XXXtypecheck_fzn(Env& env, Model* m) {
    IdMap<int> declMap;
    for (unsigned int i=0; i<m->size(); i++) {
        if (VarDeclI* vdi = (*m)[i]->dyn_cast<VarDeclI>()) {
            /*NEW MINIZINC*/vdi->e()->payload(0);
            Type t = vdi->e()->type();
            declMap.insert(vdi->e()->id(), i);
            if (t.isunknown()) {
                if (vdi->e()->ti()->domain()) {
                    switch (vdi->e()->ti()->domain()->eid()) {
#if 0 // seems to be deprecated in favour of E_SETLIT
                        case Expression::E_BINOP:
                        {
                            BinOp* bo = vdi->e()->ti()->domain()->cast<BinOp>();
                            if (bo->op()==BOT_DOTDOT) {
                                t.bt(bo->lhs()->type().bt());
                                if (t.isunknown()) {
                                    throw TypeError(env.envi(), vdi->e()->loc(), "Cannot determine type of variable declaration");
                                }
                                vdi->e()->type(t);
                                vdi->e()->ti()->type(t);
                            } else {
                                throw TypeError(env.envi(), vdi->e()->loc(), "Only ranges allowed in FlatZinc type inst");
                            }
                        }
                            break;
#endif
                        case Expression::E_ID:
                        {
                            IdMap<int>::iterator it = declMap.find(vdi->e()->ti()->domain()->cast<Id>());
                            if (it == declMap.end()) {
                                throw TypeError(env.envi(), vdi->e()->loc(), "Cannot determine type of variable declaration");
                            }
                            t.bt((*m)[it->second]->cast<VarDeclI>()->e()->type().bt());
                            if (t.isunknown()) {
                                throw TypeError(env.envi(), vdi->e()->loc(), "Cannot determine type of variable declaration");
                            }
                            vdi->e()->type(t);
                            vdi->e()->ti()->type(t);
                        }
                            break;
                        case Expression::E_SETLIT:
                        {
                            SetLit* sl = vdi->e()->ti()->domain()->cast<SetLit>();
 //debugprint(sl);
 //std::cerr << t.toString() << "\n";
                            t.bt(sl->type().bt()); // if sl->isv(), t == Type::parsetint()
                            if (t.isunknown()) { // not an int set or not a computed set
                                ASTExprVec<Expression> v = sl->v();
                                if (v.size() == 0)
                                    throw TypeError(env.envi(), vdi->e()->loc(), "Empty domain in variable declaration");
                                t.bt(v[0]->type().bt());
                            }
 //std::cerr << t.toString() << "\n";
                            vdi->e()->type(t);
                            vdi->e()->ti()->type(t);
                        }
                            break;
                        default:
                            throw TypeError(env.envi(), vdi->e()->loc(), "Cannot determine type of variable declaration");
                    }
                } else {
                    throw TypeError(env.envi(), vdi->e()->loc(), "Cannot determine type of variable declaration");
                }
            }
        }
    }
    
    struct IdDeclLink : public EVisitor {
        IdMap<int> map;
        Model* m;
        IdDeclLink(IdMap<int>& map0, Model* m0) : map(map0), m(m0) {}
        void vId(Id& id) {
            IdMap<int>::iterator it = map.find(&id);
            if (it != map.end())
                id.decl((*m)[it->second]->cast<VarDeclI>()->e());
        }
    } _iddecllink(declMap, m);
    
    struct IV : public ItemVisitor {
        IdDeclLink& il;
        IV(IdDeclLink& il0) : il(il0) {}
        /// Visit variable declaration
        void vVarDeclI(VarDeclI* vdi) {
            topDown(il, vdi->e());
        }
        /// Visit constraint item
        void vConstraintI(ConstraintI* ci) {
            topDown(il, ci->e());
            if (Call* call = ci->e()->dyn_cast<Call>()) {
                for (ExpressionSetIter p = call->ann().begin(); p != call->ann().end(); ++p)
                    if (Call* c = (*p)->dyn_cast<Call>()) {
                        if (c->id().str() == "defines_var") {
                            if (Id* id = c->args()[0]->dyn_cast<Id>()) {
                                if (!id->decl()->defined_by())
                                    id->decl()->defined_by(ci);
#if 1
                                // following is for fzn-glucose which efficiently aliases
                                // literals corresponding to its integer variable model:
                                else if (call->id().str() == "bool_eq_reif" || call->id().str() == "bool_ne_reif" || call->id().str() == "int_eq_reif" || call->id().str() == "int_ne_reif" || call->id().str() == "int_le_reif" || call->id().str() == "int_lt_reif") {
#if 0
                                    std::cout << "% typechecker warning: conflicting defines_var(" << id->str() << "): existing " << *id->decl()->defined_by()->e()->dyn_cast<Call>() << " replacing with " << *call << "\n";
#endif
                                    id->decl()->defined_by(ci);
                                }
#endif
#if 0 // yeah yeah, we know, we know
                                else
                                    std::cout << "% typechecker warning: conflicting defines_var(" << id->str() << "): existing " << *id->decl()->defined_by()->e()->dyn_cast<Call>() << " ignoring " << *call << "\n";
#endif
                            }
                        }
                    }
            }
        }
        /// Visit solve item
        void vSolveI(SolveI* si) {
            for (ExpressionSetIter p = si->ann().begin(); p != si->ann().end(); ++p)
                topDown(il, *p);
            topDown(il, si->e());
        }
    } _iv(_iddecllink);
    iterItems(_iv, m);
}

#if 0 // this isn't necessary for the MZN solver, only the FZN solver
/*static*/ bool print_sol(Problem::Problem& P, void *data) {
    PrintSolData& psd = *static_cast<PrintSolData*>(data);
    psd.output_data.clear();
    for (int i = 0; i < static_cast<int>(psd.output_spec.size()); ++i)
        psd.output_data.push_back(psd.output_spec[i].model_values(P));
    psd.output_data_valid = true;
    if (P.all_solutions) {
        {
            GCLock lock;
            Model* output_model = new Model();
            for (int i = 0; i < static_cast<int>(psd.output_spec.size()); ++i)
                output_model->addItem(psd.output_spec[i].to_assign_item(psd.output_data[i]));
            Printer p(std::cout, 0);
            p.print(output_model);
            std::cout << "----------" << std::endl;
            GC::run();
        }
        if (psd.obj_type == 0) {
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

void fzn_solver(Problem::Problem& P, std::string filename, int verbosity) {
    double initial_time = Glucose::cpuTime();

    std::vector<OutputSpec> output_spec;
    int obj_type = 0;
    Problem::Problem::IVar* obj_ivar = 0;
    {
        GCLock lock;

        /*NEW MINIZINC*/std::vector<std::string> filenames;
        filenames.push_back(filename);

        std::string std_lib_dir;
        if (char* MZNSTDLIBDIR = getenv("MZN_STDLIB_DIR"))
            std_lib_dir = std::string(MZNSTDLIBDIR);
    
        std::vector<std::string> includePaths;
        includePaths.push_back(std_lib_dir + "/std/");
    
        std::vector<std::string> datafiles;
        bool ignoreStdlib = true;
 
        /*NEW MINIZINC*/Env env;
        Model* fzn_model = parse(/*OLD MINIZINC filename,*/ /*NEW MINIZINC*/env, filenames, datafiles, includePaths, ignoreStdlib, false/*parseDocComments*/, 0/*verbose*/, std::cerr);
        if (!fzn_model)
            exit(EXIT_FAILURE); // error message has already been printed
    
        /*OLD MINIZINC Env env(fzn_model);*/
        try {
            XXXtypecheck_fzn(env, fzn_model);
        } catch (TypeError& e) {
            std::cerr << "Error: " << e.msg() << "\nIn file " << e.loc().filename.str() << ":" << e.loc().first_line << "c" << e.loc().first_column << "-" << e.loc().last_line << "c" << e.loc().last_column << std::endl;
            exit(EXIT_FAILURE);
        }
    
        EnterProblem ep(env.envi(), P, output_spec, obj_type, obj_ivar);
        iterItems<EnterProblem>(ep, fzn_model);

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
    if (verbosity > 0)
        printf("%% Parse time            : %g s\n", parsed_time - initial_time);

    std::vector<std::vector<long long> > output_data;
    bool output_data_valid = false;
    PrintSolData psd(output_spec, output_data, output_data_valid, obj_type, obj_ivar);
    bool res = P.optimize(print_sol, &psd);
    if (!P.all_solutions && output_data_valid) {
        GCLock lock;
        Model* output_model = new Model();
        for (int i = 0; i < static_cast<int>(output_spec.size()); ++i)
            output_model->addItem(output_spec[i].to_assign_item(output_data[i]));
        Printer p(std::cout, 0);
        p.print(output_model);
        std::cout << "----------" << std::endl;
        GC::run();
    } 
    if (res)
        std::cout << (output_data_valid ? "==========" : "=====UNSATISFIABLE=====") << std::endl;
}
#endif

};
