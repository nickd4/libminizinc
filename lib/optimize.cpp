/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */

/*
 *  Main authors:
 *     Guido Tack <guido.tack@monash.edu>
 */

/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include <minizinc/optimize.hh>
#include <minizinc/hash.hh>
#include <minizinc/astiterator.hh>
#include <minizinc/prettyprinter.hh>
#include <minizinc/flatten.hh>
#include <minizinc/flatten_internal.hh>
#include <minizinc/eval_par.hh>

#include <vector>

namespace MiniZinc {

  void VarOccurrences::add(VarDeclI *i, int idx_i)
  {
    idx.insert(i->e()->id(), idx_i);
  }
  void VarOccurrences::add(VarDecl *e, int idx_i)
  {
    assert(find(e) == -1);
    idx.insert(e->id(), idx_i);
  }
  int VarOccurrences::find(VarDecl* vd)
  {
    IdMap<int>::iterator it = idx.find(vd->id());
    return it==idx.end() ? -1 : it->second;
  }
  void VarOccurrences::remove(VarDecl *vd)
  {
    idx.remove(vd->id());
  }
  
  void VarOccurrences::add(VarDecl* v, Item* i) {
    IdMap<Items>::iterator vi = _m.find(v->id());
    if (vi==_m.end()) {
      Items items; items.insert(i);
      _m.insert(v->id(), items);
    } else {
      vi->second.insert(i);
    }
  }
  
  int VarOccurrences::remove(VarDecl* v, Item* i) {
    IdMap<Items>::iterator vi = _m.find(v->id());
    assert(vi!=_m.end());
    vi->second.erase(i);
    return vi->second.size();
  }
  
  void VarOccurrences::unify(Model* m, Id* id0_0, Id *id1_0) {
    Id* id0 = id0_0->decl()->id();
    Id* id1 = id1_0->decl()->id();
    
    VarDecl* v0 = id0->decl();
    VarDecl* v1 = id1->decl();

    if (v0==v1)
      return;
    
    int v0idx = find(v0);
    assert(v0idx != -1);
    (*m)[v0idx]->remove();

    IdMap<Items>::iterator vi0 = _m.find(v0->id());
    if (vi0 != _m.end()) {
      IdMap<Items>::iterator vi1 = _m.find(v1->id());
      if (vi1 == _m.end()) {
        _m.insert(v1->id(), vi0->second);
      } else {
        vi1->second.insert(vi0->second.begin(), vi0->second.end());
      }
    }
    
    id0->redirect(id1);
    
    remove(v0);
  }
  
  void VarOccurrences::clear(void) {
    _m.clear();
    idx.clear();
  }
  
  int VarOccurrences::occurrences(VarDecl* v) {
    IdMap<Items>::iterator vi = _m.find(v->id());
    return (vi==_m.end() ? 0 : vi->second.size());
  }
  
  void CollectOccurrencesI::vVarDeclI(VarDeclI* v) {
    CollectOccurrencesE ce(vo,v);
    topDown(ce,v->e());
  }
  void CollectOccurrencesI::vConstraintI(ConstraintI* ci) {
    CollectOccurrencesE ce(vo,ci);
    topDown(ce,ci->e());
  }
  void CollectOccurrencesI::vSolveI(SolveI* si) {
    CollectOccurrencesE ce(vo,si);
    topDown(ce,si->e());
    for (ExpressionSetIter it = si->ann().begin(); it != si->ann().end(); ++si)
      topDown(ce,*it);
  }

  bool isOutput(VarDecl* vd) {
    for (ExpressionSetIter it = vd->ann().begin(); it != vd->ann().end(); ++it) {
      if (*it) {
        if (*it==constants().ann.output_var)
          return true;
        if (Call* c = (*it)->dyn_cast<Call>()) {
          if (c->id() == constants().ann.output_array)
            return true;
        }
      }
      
    }
    return false;
  }
  
  void substitueFixedVars(EnvI& env, Item* ii);
  void simplifyBoolConstraint(EnvI& env, Item* ii, VarDecl* vd, bool& remove,
                              std::vector<int>& vardeclQueue,
                              std::vector<Item*>& constraintQueue,
                              std::vector<Item*>& toRemove,
                              ExpressionMap<int>& nonFixedLiteralCount);

  bool simplifyConstraint(EnvI& env, Item* ii,
                          std::vector<VarDecl*>& deletedVarDecls,
                          std::vector<Item*>& constraintQueue,
                          std::vector<int>& vardeclQueue);
  
  void unify(EnvI& env, Id* id0, Id* id1) {
    if (id0->decl() != id1->decl()) {
      if (isOutput(id0->decl())) {
        std::swap(id0,id1);
      }
      
      if (id0->decl()->e() != NULL) {
        id1->decl()->e(id0->decl()->e());
        id0->decl()->e(NULL);
      }
      
      // Compute intersection of domains
      if (id0->decl()->ti()->domain() != NULL) {
        if (id1->decl()->ti()->domain() != NULL) {
          
          if (id0->type().isint() || id0->type().isintset()) {
            IntSetVal* isv0 = eval_intset(id0->decl()->ti()->domain());
            IntSetVal* isv1 = eval_intset(id1->decl()->ti()->domain());
            IntSetRanges isv0r(isv0);
            IntSetRanges isv1r(isv1);
            Ranges::Inter<IntSetRanges,IntSetRanges> inter(isv0r,isv1r);
            IntSetVal* nd = IntSetVal::ai(inter);
            if (nd->size()==0) {
              env.addWarning("model inconsistency detected");
            } else {
              id1->decl()->ti()->domain(new SetLit(Location(), nd));
            }
          } else if (id0->type().isbool()) {
            if (eval_bool(id0->decl()->ti()->domain()) != eval_bool(id1->decl()->ti()->domain()))
              env.addWarning("model inconsistency detected");
          } else {
            // float
            BinOp* dom0 = id0->decl()->ti()->domain()->cast<BinOp>();
            BinOp* dom1 = id1->decl()->ti()->domain()->cast<BinOp>();
            FloatVal lb0 = dom0->lhs()->cast<FloatLit>()->v();
            FloatVal ub0 = dom0->rhs()->cast<FloatLit>()->v();
            FloatVal lb1 = dom1->lhs()->cast<FloatLit>()->v();
            FloatVal ub1 = dom1->rhs()->cast<FloatLit>()->v();
            FloatVal lb = std::max(lb0,lb1);
            FloatVal ub = std::min(ub0,ub1);
            if (lb != lb1 || ub != ub1) {
              BinOp* newdom = new BinOp(Location(), new FloatLit(Location(),lb), BOT_DOTDOT, new FloatLit(Location(),ub));
              newdom->type(Type::parsetfloat());
              id1->decl()->ti()->domain(newdom);
            }
          }
          
        } else {
          id1->decl()->ti()->domain(id0->decl()->ti()->domain());
        }
      }
      
      // If both variables are output variables, unify them in the output model
      if (isOutput(id0->decl())) {
        assert(env.output_vo.find(id0->decl()) != -1);
        VarDecl* id0_output = (*env.output)[env.output_vo.find(id0->decl())]->cast<VarDeclI>()->e();
        assert(env.output_vo.find(id1->decl()) != -1);
        VarDecl* id1_output = (*env.output)[env.output_vo.find(id1->decl())]->cast<VarDeclI>()->e();
        if (id0_output->e() == NULL) {
          id0_output->e(id1_output->id());
        }
      }
      
      env.vo.unify(env.flat(), id0, id1);
    }
  }

  void pushVarDecl(EnvI& env, VarDeclI* vdi, int vd_idx, std::vector<int>& q) {
    if (!vdi->removed() && !vdi->flag())
      q.push_back(vd_idx);
  }
  void pushVarDecl(EnvI& env, int vd_idx, std::vector<int>& q) {
    pushVarDecl(env, (*env.flat())[vd_idx]->cast<VarDeclI>(), vd_idx, q);
  }
  
  void pushDependentConstraints(EnvI& env, Id* id, std::vector<Item*>& q) {
    IdMap<VarOccurrences::Items>::iterator it = env.vo._m.find(id);
    if (it != env.vo._m.end()) {
      for (VarOccurrences::Items::iterator item = it->second.begin(); item != it->second.end(); ++item) {
        if (ConstraintI* ci = (*item)->dyn_cast<ConstraintI>()) {
          if (!ci->removed() && !ci->flag()) {
            ci->flag(true);
            q.push_back(ci);
          }
        } else if (VarDeclI* vdi = (*item)->dyn_cast<VarDeclI>()) {
          if (!vdi->removed() && !vdi->flag() && vdi->e()->e() && vdi->e()->e()->isa<Call>()) {
            vdi->flag(true);
            q.push_back(vdi);
          }
        }
      }
    }
    
  }
  
  void optimize(Env& env) {
    EnvI& envi = env.envi();
    Model& m = *envi.flat();
    std::vector<int> toAssignBoolVars;
    std::vector<int> toRemoveConstraints;
    std::vector<VarDecl*> deletedVarDecls;

    std::vector<Item*> constraintQueue;
    std::vector<int> vardeclQueue;
    
    GCLock lock;

    for (unsigned int i=0; i<m.size(); i++) {
      if (m[i]->removed())
        continue;
      if (ConstraintI* ci = m[i]->dyn_cast<ConstraintI>()) {
        ci->flag(false);
        if (!ci->removed()) {
          if (Call* c = ci->e()->dyn_cast<Call>()) {
            if ( (c->id() == constants().ids.int_.eq || c->id() == constants().ids.bool_eq || c->id() == constants().ids.float_.eq || c->id() == constants().ids.set_eq) &&
                c->args()[0]->isa<Id>() && c->args()[1]->isa<Id>() &&
                (c->args()[0]->cast<Id>()->decl()->e()==NULL || c->args()[1]->cast<Id>()->decl()->e()==NULL) ) {
              unify(envi, c->args()[0]->cast<Id>(), c->args()[1]->cast<Id>());
              pushDependentConstraints(envi, c->args()[0]->cast<Id>(), constraintQueue);
              CollectDecls cd(envi.vo,deletedVarDecls,ci);
              topDown(cd,c);
              ci->e(constants().lit_true);
              ci->remove();
            } else if (c->id()==constants().ids.forall) {
              ArrayLit* al = follow_id(c->args()[0])->cast<ArrayLit>();
              for (unsigned int i=al->v().size(); i--;) {
                if (Id* id = al->v()[i]->dyn_cast<Id>()) {
                  if (id->decl()->ti()->domain()==NULL) {
                    toAssignBoolVars.push_back(envi.vo.idx.find(id->decl()->id())->second);
                  } else if (id->decl()->ti()->domain() == constants().lit_false) {
                    envi.addWarning("model inconsistency detected");
                    id->decl()->e(constants().lit_true);
                  }
                }
              }
              toRemoveConstraints.push_back(i);
            }
          } else if (Id* id = ci->e()->dyn_cast<Id>()) {
            if (id->decl()->ti()->domain() == constants().lit_false) {
              envi.addWarning("model inconsistency detected");
              ci->e(constants().lit_false);
            } else {
              if (id->decl()->ti()->domain()==NULL) {
                toAssignBoolVars.push_back(envi.vo.idx.find(id->decl()->id())->second);
              }
              toRemoveConstraints.push_back(i);
            }
          }
        }
      } else if (VarDeclI* vdi = m[i]->dyn_cast<VarDeclI>()) {
        vdi->flag(false);
        if (vdi->e()->e() && vdi->e()->e()->isa<Id>() && vdi->e()->type().dim()==0) {
          Id* id1 = vdi->e()->e()->cast<Id>();
          vdi->e()->e(NULL);
          unify(envi, vdi->e()->id(), id1);
          pushDependentConstraints(envi, id1, constraintQueue);
        }
        if (vdi->e()->type().isbool() && vdi->e()->type().isvar() && vdi->e()->type().dim()==0
            && (vdi->e()->ti()->domain() == constants().lit_true || vdi->e()->ti()->domain() == constants().lit_false)) {
          pushVarDecl(envi, vdi, i, vardeclQueue);
          pushDependentConstraints(envi, vdi->e()->id(), constraintQueue);
        }
      }
    }
    for (unsigned int i=toAssignBoolVars.size(); i--;) {
      if (m[toAssignBoolVars[i]]->removed())
        continue;
      VarDeclI* vdi = m[toAssignBoolVars[i]]->cast<VarDeclI>();
      if (vdi->e()->ti()->domain()==NULL) {
        vdi->e()->ti()->domain(constants().lit_true);
        pushVarDecl(envi, vdi, toAssignBoolVars[i], vardeclQueue);
        pushDependentConstraints(envi, vdi->e()->id(), constraintQueue);
      }
    }
    
    ExpressionMap<int> nonFixedLiteralCount;
    while (!vardeclQueue.empty() || !constraintQueue.empty()) {
      while (!vardeclQueue.empty()) {
        int var_idx = vardeclQueue.back();
        vardeclQueue.pop_back();
        m[var_idx]->cast<VarDeclI>()->flag(false);
        VarDecl* vd = m[var_idx]->cast<VarDeclI>()->e();
        
        if (vd->type().isbool()) {
          bool isTrue = vd->ti()->domain() == constants().lit_true;
          bool remove = false;
          if (vd->e()) {
            if (Id* id = vd->e()->dyn_cast<Id>()) {
              if (id->decl()->ti()->domain()==NULL) {
                id->decl()->ti()->domain(vd->ti()->domain());
                pushVarDecl(envi, envi.vo.idx.find(id->decl()->id())->second, vardeclQueue);
                remove = true;
              } else if (id->decl()->ti()->domain() != vd->ti()->domain()) {
                envi.addWarning("model inconsistency detected");
                remove = false;
              } else {
                remove = true;
              }
            } else if (Call* c = vd->e()->dyn_cast<Call>()) {
              if (isTrue && c->id()==constants().ids.forall) {
                remove = true;
                ArrayLit* al = follow_id(c->args()[0])->cast<ArrayLit>();
                for (unsigned int i=0; i<al->v().size(); i++) {
                  if (Id* id = al->v()[i]->dyn_cast<Id>()) {
                    if (id->decl()->ti()->domain()==NULL) {
                      id->decl()->ti()->domain(constants().lit_true);
                      pushVarDecl(envi, envi.vo.idx.find(id->decl()->id())->second, vardeclQueue);
                    } else if (id->decl()->ti()->domain() == constants().lit_false) {
                      envi.addWarning("model inconsistency detected");
                      remove = false;
                    }
                  }
                }
              } else if (!isTrue && (c->id()==constants().ids.exists || c->id()==constants().ids.clause)) {
                remove = true;
                for (unsigned int i=0; i<c->args().size(); i++) {
                  bool ispos = i==0;
                  ArrayLit* al = follow_id(c->args()[i])->cast<ArrayLit>();
                  for (unsigned int j=0; j<al->v().size(); j++) {
                    if (Id* id = al->v()[j]->dyn_cast<Id>()) {
                      if (id->decl()->ti()->domain()==NULL) {
                        id->decl()->ti()->domain(constants().boollit(!ispos));
                        pushVarDecl(envi, envi.vo.idx.find(id->decl()->id())->second, vardeclQueue);
                      } else if (id->decl()->ti()->domain() == constants().boollit(ispos)) {
                        envi.addWarning("model inconsistency detected");
                        remove = false;
                      }
                    }
                  }
                }
              }
            }
          } else {
            remove = true;
          }
          pushDependentConstraints(envi, vd->id(), constraintQueue);
          std::vector<Item*> toRemove;
          IdMap<VarOccurrences::Items>::iterator it = envi.vo._m.find(vd->id());
          if (it != envi.vo._m.end()) {
            for (VarOccurrences::Items::iterator item = it->second.begin(); item != it->second.end(); ++item) {
              if (VarDeclI* vdi = (*item)->dyn_cast<VarDeclI>()) {
                if (vdi->e()->e() && vdi->e()->e()->isa<ArrayLit>()) {
                  IdMap<VarOccurrences::Items>::iterator ait = envi.vo._m.find(vdi->e()->id());
                  if (ait != envi.vo._m.end()) {
                    for (VarOccurrences::Items::iterator aitem = ait->second.begin(); aitem != ait->second.end(); ++aitem) {
                      simplifyBoolConstraint(envi,*aitem,vd,remove,vardeclQueue,constraintQueue,toRemove,nonFixedLiteralCount);
                    }
                  }
                  continue;
                }
              }
              simplifyBoolConstraint(envi,*item,vd,remove,vardeclQueue,constraintQueue,toRemove,nonFixedLiteralCount);
            }
          }
          for (unsigned int i=toRemove.size(); i--;) {
            if (ConstraintI* ci = toRemove[i]->dyn_cast<ConstraintI>()) {
              CollectDecls cd(envi.vo,deletedVarDecls,ci);
              topDown(cd,ci->e());
              ci->remove();
            } else {
              VarDeclI* vdi = toRemove[i]->cast<VarDeclI>();
              CollectDecls cd(envi.vo,deletedVarDecls,vdi);
              topDown(cd,vdi->e()->e());
              vdi->e()->e(NULL);
            }
          }
          if (remove) {
            deletedVarDecls.push_back(vd);
          } else {
            simplifyConstraint(envi,m[var_idx],deletedVarDecls,constraintQueue,vardeclQueue);
          }
        }
      }
      bool handledConstraint = false;
      while (!handledConstraint && !constraintQueue.empty()) {
        Item* item = constraintQueue.back();
        constraintQueue.pop_back();
        if (ConstraintI* ci = item->dyn_cast<ConstraintI>()) {
          ci->flag(false);
        } else {
          item->cast<VarDeclI>()->flag(false);
        }
        substitueFixedVars(envi, item);
        handledConstraint = simplifyConstraint(envi,item,deletedVarDecls,constraintQueue,vardeclQueue);
      }
    }
    for (unsigned int i=toRemoveConstraints.size(); i--;) {
      ConstraintI* ci = m[toRemoveConstraints[i]]->cast<ConstraintI>();
      CollectDecls cd(envi.vo,deletedVarDecls,ci);
      topDown(cd,ci->e());
      ci->remove();
    }
    
    while (!deletedVarDecls.empty()) {
      VarDecl* cur = deletedVarDecls.back(); deletedVarDecls.pop_back();
      if (envi.vo.occurrences(cur) == 0 && !isOutput(cur)) {
        IdMap<int>::iterator cur_idx = envi.vo.idx.find(cur->id());
        if (cur_idx != envi.vo.idx.end() && !m[cur_idx->second]->removed()) {
          CollectDecls cd(envi.vo,deletedVarDecls,m[cur_idx->second]->cast<VarDeclI>());
          topDown(cd,cur->e());
          m[cur_idx->second]->remove();
        }
      }
    }
  }

  class SubstitutionVisitor : public EVisitor {
  protected:
    Expression* subst(Expression* e) {
      if (VarDecl* vd = follow_id_to_decl(e)->dyn_cast<VarDecl>()) {
        if (vd->type().isbool() && vd->ti()->domain())
          return vd->ti()->domain();
        if (vd->type().isint()) {
          if (vd->e() && vd->e()->isa<IntLit>())
            return vd->e();
          if (vd->ti()->domain() && vd->ti()->domain()->isa<SetLit>() &&
              vd->ti()->domain()->cast<SetLit>()->isv()->size()==1 &&
              vd->ti()->domain()->cast<SetLit>()->isv()->min()==vd->ti()->domain()->cast<SetLit>()->isv()->max()) {
            return new IntLit(Location().introduce(),vd->ti()->domain()->cast<SetLit>()->isv()->min());
          }
        }
      }
      return e;
    }
  public:
    /// Visit array literal
    void vArrayLit(const ArrayLit& al) {
      for (unsigned int i=0; i<al.v().size(); i++) {
        al.v()[i] = subst(al.v()[i]);
      }
    }
    /// Visit call
    void vCall(const Call& c) {
      for (unsigned int i=0; i<c.args().size(); i++) {
        c.args()[i] = subst(c.args()[i]);
      }
    }
    /// Determine whether to enter node
    bool enter(Expression* e) {
      return !e->isa<Id>();
    }
  };
  
  void substitueFixedVars(EnvI& env, Item* ii) {
    SubstitutionVisitor sv;
    if (ConstraintI* ci = ii->dyn_cast<ConstraintI>()) {
      topDown(sv, ci->e());
      for (ExpressionSetIter it = ci->e()->ann().begin(); it != ci->e()->ann().end(); ++it) {
        topDown(sv, *it);
      }
    } else if (VarDeclI* vdi = ii->dyn_cast<VarDeclI>()) {
      topDown(sv, vdi->e());
      for (ExpressionSetIter it = vdi->e()->ann().begin(); it != vdi->e()->ann().end(); ++it) {
        topDown(sv, *it);
      }
    } else {
      SolveI* si = ii->cast<SolveI>();
      topDown(sv, si->e());
      for (ExpressionSetIter it = si->ann().begin(); it != si->ann().end(); ++it) {
        topDown(sv, *it);
      }
    }
  }
  
  bool simplifyConstraint(EnvI& env, Item* ii,
                          std::vector<VarDecl*>& deletedVarDecls,
                          std::vector<Item*>& constraintQueue,
                          std::vector<int>& vardeclQueue) {
    Expression* con_e = ii->isa<ConstraintI>() ? ii->cast<ConstraintI>()->e() : ii->cast<VarDeclI>()->e()->e();
    if (Call* c = Expression::dyn_cast<Call>(con_e)) {
      if (c->id()==constants().ids.int_.lin_le ||
          c->id()==constants().ids.int_.lin_eq ||
          c->id()==constants().ids.int_.lin_ne) {
        ArrayLit* al_c = eval_array_lit(c->args()[0]);
        std::vector<IntVal> coeffs(al_c->v().size());
        for (unsigned int i=0; i<al_c->v().size(); i++) {
          coeffs[i] = eval_int(al_c->v()[i]);
        }
        ArrayLit* al_x = eval_array_lit(c->args()[1]);
        std::vector<KeepAlive> x(al_x->v().size());
        for (unsigned int i=0; i<al_x->v().size(); i++) {
          x[i] = al_x->v()[i];
        }
        IntVal d = 0;
        simplify_lin<IntLit>(coeffs, x, d);
        if (coeffs.size() < al_c->v().size()) {
          std::vector<Expression*> coeffs_e(coeffs.size());
          std::vector<Expression*> x_e(coeffs.size());
          for (unsigned int i=0; i<coeffs.size(); i++) {
            coeffs_e[i] = new IntLit(Location().introduce(),coeffs[i]);
            x_e[i] = x[i]();
          }
          ArrayLit* al_c_new = new ArrayLit(al_c->loc(),coeffs_e);
          al_c_new->type(Type::parint(1));
          ArrayLit* al_x_new = new ArrayLit(al_x->loc(),x_e);
          al_x_new->type(al_x->type());
          c->args()[0] = al_c_new;
          c->args()[1] = al_x_new;
          if (d != 0) {
            c->args()[2] = new IntLit(Location().introduce(), eval_int(c->args()[2])-d);
          }
        }
        return true;
      } else if ( (c->id() == constants().ids.int_.eq || c->id() == constants().ids.bool_eq || c->id() == constants().ids.float_.eq || c->id() == constants().ids.set_eq) &&
          c->args()[0]->isa<Id>() && c->args()[1]->isa<Id>() &&
          (c->args()[0]->cast<Id>()->decl()->e()==NULL || c->args()[1]->cast<Id>()->decl()->e()==NULL) ) {
        unify(env, c->args()[0]->cast<Id>(), c->args()[1]->cast<Id>());
        pushDependentConstraints(env, c->args()[0]->cast<Id>(), constraintQueue);
        CollectDecls cd(env.vo,deletedVarDecls,ii);
        topDown(cd,c);
        ii->remove();
      } else if (c->id() == constants().ids.int_.eq && (( c->args()[0]->isa<IntLit>() && c->args()[1]->isa<Id>() ) ||
                                                        ( c->args()[1]->isa<IntLit>() && c->args()[0]->isa<Id>() ) ) ) {
        Id* ident = c->args()[0]->isa<Id>() ? c->args()[0]->cast<Id>() : c->args()[1]->cast<Id>();
        IntVal d = c->args()[0]->isa<IntLit>() ? eval_int(c->args()[0]) : eval_int(c->args()[1]);
        if (ident->decl()->e()==NULL) {
          ident->decl()->e(c->args()[0]->isa<IntLit>() ? c->args()[0] : c->args()[1]);
        }
        if (ident->decl()->ti()->domain() == NULL) {
          ident->decl()->ti()->domain(new SetLit(Location().introduce(), IntSetVal::a(d,d)));
        } else {
          IntSetVal* isv = eval_intset(ident->decl()->ti()->domain());
          if (isv->contains(d)) {
            ident->decl()->ti()->domain(new SetLit(Location().introduce(), IntSetVal::a(d,d)));
          } else {
            env.addWarning("model inconsistency detected");
          }
        }
        
        pushDependentConstraints(env, ident, constraintQueue);
        CollectDecls cd(env.vo,deletedVarDecls,ii);
        topDown(cd,c);
        ii->remove();
      }
    }
    return false;
  }
  
  int boolState(Expression* e) {
    if (e->type().ispar()) {
      return eval_bool(e);
    } else {
      Id* id = e->cast<Id>();
      if (id->decl()->ti()->domain()==NULL)
        return 2;
      return id->decl()->ti()->domain()==constants().lit_true;
    }
  }

  int decrementNonFixedVars(ExpressionMap<int>& nonFixedLiteralCount, Call* c) {
    ExpressionMap<int>::iterator it = nonFixedLiteralCount.find(c);
    if (it==nonFixedLiteralCount.end()) {
      int nonFixedVars = 0;
      for (unsigned int i=0; i<c->args().size(); i++) {
        ArrayLit* al = follow_id(c->args()[i])->cast<ArrayLit>();
        nonFixedVars += al->v().size();
        for (unsigned int j=al->v().size(); j--;) {
          if (al->v()[j]->type().ispar())
            nonFixedVars--;
        }
      }
      nonFixedVars--; // for the identifier we're currently processing
      nonFixedLiteralCount.insert(c, nonFixedVars);
      return nonFixedVars;
    } else {
      it->second--;
      return it->second;
    }
  }

  void simplifyBoolConstraint(EnvI& env, Item* ii, VarDecl* vd, bool& remove,
                              std::vector<int>& vardeclQueue,
                              std::vector<Item*>& constraintQueue,
                              std::vector<Item*>& toRemove,
                              ExpressionMap<int>& nonFixedLiteralCount) {
    if (ii->isa<SolveI>()) {
      remove = false;
      return;
    }
    bool isTrue = vd->ti()->domain()==constants().lit_true;
    Expression* e = NULL;
    ConstraintI* ci = ii->dyn_cast<ConstraintI>();
    VarDeclI* vdi = ii->dyn_cast<VarDeclI>();
    if (ci) {
      e = ci->e();
    } else if (vdi) {
      e = vdi->e()->e();
      if (e==NULL)
        return;
      if (Id* id = e->dyn_cast<Id>()) {
        assert(id->decl()==vd);
        if (vdi->e()->ti()->domain()==NULL) {
          vdi->e()->ti()->domain(constants().boollit(isTrue));
          vardeclQueue.push_back(env.vo.idx.find(vdi->e()->id())->second);
        } else if (id->decl()->ti()->domain() == constants().boollit(!isTrue)) {
          env.addWarning("model inconsistency detected");
          remove = false;
        }
        return;
      }
    }
    if (Id* ident = e->dyn_cast<Id>()) {
      assert(ident->decl() == vd);
      return;
    }
    Call* c = e->cast<Call>();
    if (c->id()==constants().ids.bool_eq) {
      Expression* b0 = c->args()[0];
      Expression* b1 = c->args()[1];
      int b0s = boolState(b0);
      int b1s = boolState(b1);
      if (b0s==2) {
        std::swap(b0,b1);
        std::swap(b0s,b1s);
      }
      assert(b0s!=2);
      if (ci || vdi->e()->ti()->domain()==constants().lit_true) {
        if (b0s != b1s) {
          if (b1s==2) {
            b1->cast<Id>()->decl()->ti()->domain(constants().boollit(isTrue));
            vardeclQueue.push_back(env.vo.idx.find(b1->cast<Id>()->decl()->id())->second);
            if (ci)
              toRemove.push_back(ci);
          } else {
            env.addWarning("model inconsistency detected");
            remove = false;
          }
        } else {
          if (ci)
            toRemove.push_back(ci);
        }
      } else if (vdi && vdi->e()->ti()->domain()==constants().lit_false) {
        if (b0s != b1s) {
          if (b1s==2) {
            b1->cast<Id>()->decl()->ti()->domain(constants().boollit(isTrue));
            vardeclQueue.push_back(env.vo.idx.find(b1->cast<Id>()->decl()->id())->second);
          }
        } else {
          env.addWarning("model inconsistency detected");
          remove = false;
        }
      } else {
        remove = false;
      }
    } else if (c->id()==constants().ids.forall || c->id()==constants().ids.exists || c->id()==constants().ids.clause) {
      if (isTrue && c->id()==constants().ids.exists) {
        if (ci) {
          toRemove.push_back(ci);
        } else {
          if (vdi->e()->ti()->domain()==NULL) {
            vdi->e()->ti()->domain(constants().lit_true);
            vardeclQueue.push_back(env.vo.idx.find(vdi->e()->id())->second);
          } else if (vdi->e()->ti()->domain()!=constants().lit_true) {
            env.addWarning("model inconsistency detected");
            vdi->e()->e(constants().lit_true);
          }
        }
      } else if (!isTrue && c->id()==constants().ids.forall) {
        if (ci) {
          env.addWarning("model inconsistency detected");
          toRemove.push_back(ci);
        } else {
          if (vdi->e()->ti()->domain()==NULL) {
            vdi->e()->ti()->domain(constants().lit_false);
            vardeclQueue.push_back(env.vo.idx.find(vdi->e()->id())->second);
          } else if (vdi->e()->ti()->domain()!=constants().lit_false) {
            env.addWarning("model inconsistency detected");
            vdi->e()->e(constants().lit_false);
          }
        }
      } else {
        int nonfixed = decrementNonFixedVars(nonFixedLiteralCount,c);
        bool isConjunction = (c->id() == constants().ids.forall);
        assert(nonfixed >=0);
        if (nonfixed<=1) {
          bool subsumed = false;
          int nonfixed_i=-1;
          int nonfixed_j=-1;
          int realNonFixed = 0;
          for (unsigned int i=0; i<c->args().size(); i++) {
            bool unit = (i==0 ? isConjunction : !isConjunction);
            ArrayLit* al = follow_id(c->args()[i])->cast<ArrayLit>();
            realNonFixed += al->v().size();
            for (unsigned int j=al->v().size(); j--;) {
              if (al->v()[j]->type().ispar() || al->v()[j]->cast<Id>()->decl()->ti()->domain())
                realNonFixed--;
              if (al->v()[j]->type().ispar() && eval_bool(al->v()[j]) != unit) {
                subsumed = true;
                i=2; // break out of outer loop
                break;
              } else if (Id* id = al->v()[j]->dyn_cast<Id>()) {
                if (id->decl()->ti()->domain()) {
                  bool idv = (id->decl()->ti()->domain()==constants().lit_true);
                  if (unit != idv) {
                    subsumed = true;
                    i=2; // break out of outer loop
                    break;
                  }
                } else {
                  nonfixed_i = i;
                  nonfixed_j = j;
                }
              }
            }
          }
          
          if (subsumed) {
            if (ci) {
              if (isConjunction) {
                env.addWarning("model inconsistency detected");
                ci->e(constants().lit_false);
              } else {
                toRemove.push_back(ci);
              }
            } else {
              if (vdi->e()->ti()->domain()==NULL) {
                vdi->e()->ti()->domain(constants().boollit(!isConjunction));
                vardeclQueue.push_back(env.vo.idx.find(vdi->e()->id())->second);
              } else if (vdi->e()->ti()->domain()!=constants().boollit(!isConjunction)) {
                env.addWarning("model inconsistency detected");
                vdi->e()->e(constants().boollit(!isConjunction));
              }
            }
          } else if (realNonFixed==0) {
            if (ci) {
              if (isConjunction) {
                toRemove.push_back(ci);
              } else {
                env.addWarning("model inconsistency detected");
                ci->e(constants().lit_false);
              }
            } else {
              if (vdi->e()->ti()->domain()==NULL) {
                vdi->e()->ti()->domain(constants().boollit(isConjunction));
                vardeclQueue.push_back(env.vo.idx.find(vdi->e()->id())->second);
              } else if (vdi->e()->ti()->domain()!=constants().boollit(isConjunction)) {
                env.addWarning("model inconsistency detected");
                vdi->e()->e(constants().boollit(isConjunction));
              }
            }
          } else {
            // not subsumed, nonfixed==1
            assert(nonfixed_i != -1);
            ArrayLit* al = follow_id(c->args()[nonfixed_i])->cast<ArrayLit>();
            Id* id = al->v()[nonfixed_j]->cast<Id>();
            if (ci || vdi->e()->ti()->domain()) {
              bool result = nonfixed_i==0;
              if (vdi && vdi->e()->ti()->domain()==constants().lit_false)
                result = !result;
              VarDecl* vd = id->decl();
              if (vd->ti()->domain()==NULL) {
                vd->ti()->domain(constants().boollit(result));
                vardeclQueue.push_back(env.vo.idx.find(vd->id())->second);
              } else if (vd->ti()->domain()!=constants().boollit(result)) {
                env.addWarning("model inconsistency detected");
                vd->e(constants().lit_true);
              }
            } else {
              vdi->e()->e(id);
            }
          }
          
        } else if (c->id()==constants().ids.clause) {
          int posOrNeg = isTrue ? 0 : 1;
          ArrayLit* al = follow_id(c->args()[posOrNeg])->cast<ArrayLit>();
          ArrayLit* al_other = follow_id(c->args()[1-posOrNeg])->cast<ArrayLit>();
          
          if (ci && al->v().size()==1 && al->v()[0]!=vd->id() && al_other->v().size()==1) {
            // simple implication
            assert(al_other->v()[0]==vd->id());
            if (ci) {
              if (al->v()[0]->type().ispar()) {
                if (eval_bool(al->v()[0])==isTrue) {
                  toRemove.push_back(ci);
                } else {
                  env.addWarning("model inconsistency detected");
                  remove = false;
                }
              } else {
                Id* id = al->v()[0]->cast<Id>();
                if (id->decl()->ti()->domain()==NULL) {
                  id->decl()->ti()->domain(constants().boollit(isTrue));
                  vardeclQueue.push_back(env.vo.idx.find(id->decl()->id())->second);
                } else {
                  if (id->decl()->ti()->domain()==constants().boollit(isTrue)) {
                    toRemove.push_back(ci);
                  } else {
                    env.addWarning("model inconsistency detected");
                    remove = false;
                  }
                }
              }
            }
          } else {
            // proper clause
            for (unsigned int i=0; i<al->v().size(); i++) {
              if (al->v()[i]==vd->id()) {
                if (ci) {
                  toRemove.push_back(ci);
                } else {
                  if (vdi->e()->ti()->domain()==NULL) {
                    vdi->e()->ti()->domain(constants().lit_true);
                    vardeclQueue.push_back(env.vo.idx.find(vdi->e()->id())->second);
                  } else if (vdi->e()->ti()->domain()!=constants().lit_true) {
                    env.addWarning("model inconsistency detected");
                    vdi->e()->e(constants().lit_true);
                  }
                }
                break;
              }
            }
          }
        }
      }
    } else {
      remove = false;
    }
  }

}
