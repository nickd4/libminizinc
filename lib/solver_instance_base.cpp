/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */

/*
 *  Main authors:
 *     Guido Tack <guido.tack@monash.edu>
 */

/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include <minizinc/solver_instance_base.hh>
#include <minizinc/eval_par.hh>

#ifdef _MSC_VER 
#define _CRT_SECURE_NO_WARNINGS
#undef ERROR    // MICROsoft.
#undef min
#undef max
#endif

namespace MiniZinc {

  SolverInstanceBase::Status
  SolverInstanceBase::solve(void) { return SolverInstance__ERROR; }
  
  void
  SolverInstanceBase::reset(void) { assert(false); }
  
  void
  SolverInstanceBase::resetWithConstraints(Model::iterator begin, Model::iterator end) {
    assert(false);
  }

  void
  SolverInstanceBase::processPermanentConstraints(Model::iterator begin, Model::iterator end) {
    assert(false);
  }
  
  void
  Registry::add(const ASTString& name, poster p) {
    _registry.insert(std::make_pair(name, p));
  }
  void
  Registry::post(Call* c) {
    ASTStringMap<poster>::t::iterator it = _registry.find(c->id());
    if (it == _registry.end()) {
      std::cerr << "Error: constraint not found: " << c->id() << "\n";
      exit(EXIT_FAILURE);
    }
    it->second(_base, c);
  }

  void SolverInstanceBase::printSolution() {
    if ( 0==pS2Out ) {
      getEnv()->evalOutput(std::cout);               // deprecated
      std::cout << "----------" << std::endl;
    }
    else
      getSolns2Out()->evalOutput();
    if ( getOptions().getBoolParam(constants().opts.statistics.str()) )
      printStatistics(std::cout, 1);
  }

  void SolverInstanceBase2::printSolution() {
    GCLock lock;
    assignSolutionToOutput();
    SolverInstanceBase::printSolution();
  }

//   void
//   SolverInstanceBase::assignSolutionToOutput(void) {
//     for (VarDeclIterator it = getEnv()->output()->begin_vardecls(); it != getEnv()->output()->end_vardecls(); ++it) {
//       if (it->e()->e() == NULL) {
//         it->e()->e(getSolutionValue(it->e()->id()));
//       }
//     }
//   }
  
  void SolverInstanceBase1::assignSolutionToOutput() {
    
    MZN_ASSERT_HARD_MSG( 0!=pS2Out, "Setup a Solns2Out object to use default solution extraction/reporting procs" );
    
    pS2Out->declNewOutput();  // Even for empty output decl
    
    //iterate over set of ids that have an output annotation && obtain their right hand side from the flat model
    for (VarDeclIterator it = getEnv()->flat()->begin_vardecls(); it != getEnv()->flat()->end_vardecls(); ++it) {
      if(!it->removed()) {
        VarDecl* vd = it->e();
        if(vd->ann().containsCall(constants().ann.output_array.aststr()) ||
            vd->ann().contains(constants().ann.output_var)
          ) {
          //std::cout << "DEBUG: Looking at var-decl with output-annotation: " << *vd << std::endl;
          if(Call* output_array_ann = Expression::dyn_cast<Call>(getAnnotation(vd->ann(), constants().ann.output_array.aststr()))) {
            assert(vd->e());
            if(ArrayLit* al = vd->e()->dyn_cast<ArrayLit>()) {
              std::vector<Expression*> array_elems;
              ASTExprVec<Expression> array = al->v();
              for(unsigned int i=0; i<array.size(); i++) {
                if(Id* id = array[i]->dyn_cast<Id>()) {
                  //std::cout << "DEBUG: getting solution value from " << *id  << " : " << id->v() << std::endl;
                  array_elems.push_back(getSolutionValue(id));
                } else if(FloatLit* floatLit = array[i]->dyn_cast<FloatLit>()) {
                  array_elems.push_back(floatLit);
                } else if(IntLit* intLit = array[i]->dyn_cast<IntLit>()) {
                  array_elems.push_back(intLit);
                } else if(BoolLit* boolLit = array[i]->dyn_cast<BoolLit>()) {
                  array_elems.push_back(boolLit);
                } else if(SetLit* setLit = array[i]->dyn_cast<SetLit>()) {
                  array_elems.push_back(setLit);
                } else if(StringLit* strLit = array[i]->dyn_cast<StringLit>()) {
                  array_elems.push_back(strLit);
                } else {
                  std::cerr << "Error: array element " << *array[i] << " is ! an id nor a literal" << std::endl;
                  assert(false);
                }
              }
              GCLock lock;
              ArrayLit* dims;
              Expression* e = output_array_ann->args()[0];
              if(ArrayLit* al = e->dyn_cast<ArrayLit>()) {
                dims = al;
              } else if(Id* id = e->dyn_cast<Id>()) {
                dims = id->decl()->e()->cast<ArrayLit>();
              } else {
                throw -1;
              }
              std::vector<std::pair<int,int> > dims_v;
              for( int i=0;i<dims->length();i++) {
                IntSetVal* isv = eval_intset(getEnv()->envi(), dims->v()[i]);
                if (isv->size()==0) {
                  dims_v.push_back(std::pair<int,int>(1,0));
                } else {
                  dims_v.push_back(std::pair<int,int>(isv->min().toInt(),isv->max().toInt()));
                }
              }
              ArrayLit* array_solution = new ArrayLit(Location(),array_elems,dims_v);
              KeepAlive ka(array_solution);
              auto& de = getSolns2Out()->findOutputVar(vd->id()->str().str());
              de.first->e(array_solution);
            }
          } else if(vd->ann().contains(constants().ann.output_var)) {
            Expression* sol = getSolutionValue(vd->id());
            vd->e(sol);
            auto& de = getSolns2Out()->findOutputVar(vd->id()->str().str());
            de.first->e(sol);
          }
        }
      }
    }
  }

 void 
  SolverInstanceBase::flattenSearchAnnotations(const Annotation& ann, std::vector<Expression*>& out) {
    for(ExpressionSetIter i = ann.begin(); i != ann.end(); ++i) {
        Expression* e = *i;
        if(e->isa<Call>() && e->cast<Call>()->id().str() == "seq_search") {
            Call* c = e->cast<Call>();
            ArrayLit* anns = c->args()[0]->cast<ArrayLit>();
            for(unsigned int i=0; i<anns->v().size(); i++) {
                Annotation subann;
                subann.add(anns->v()[i]);
                flattenSearchAnnotations(subann, out);
            }
        } else {
            out.push_back(*i);
        }
    }
  }


}  // namespace MiniZinc
