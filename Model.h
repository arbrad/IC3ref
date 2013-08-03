/*********************************************************************
Copyright (c) 2013, Aaron Bradley

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*********************************************************************/

#ifndef MODEL_H_INCLUDED
#define MODEL_H_INCLUDED

#include <algorithm>
#include <set>
#include <sstream>
#include <unordered_map>
#include <vector>

extern "C" {
#include "aiger.h"
}
#include "Solver.h"
#include "SimpSolver.h"

// Read it and weep: yes, it's in a header file; no, I don't want to
// have std:: all over the place.
using namespace std;

// A row of the AIGER spec: lhs = rhs0 & rhs1.
struct AigRow {
  AigRow(Minisat::Lit _lhs, Minisat::Lit _rhs0, Minisat::Lit _rhs1) :
    lhs(_lhs), rhs0(_rhs0), rhs1(_rhs1) {}
  Minisat::Lit lhs, rhs0, rhs1;
};
// Intended to hold the AND section of an AIGER spec.
typedef vector<AigRow> AigVec;
typedef vector<Minisat::Lit> LitVec;

// A lightweight wrapper around Minisat::Var that includes a name.
class Var {
public:
  Var(const string name) {
    _var = gvi++;
    _name = name;
  }
  size_t index() const { return (size_t) _var; }
  Minisat::Var var() const { return _var; }
  Minisat::Lit lit(bool neg) const {
    return Minisat::mkLit(_var, neg);
  }
  string name() const { return _name; }
private:
  static Minisat::Var gvi;  // aligned with solvers
  Minisat::Var _var;        // corresponding Minisat::Var in *any* solver
  string _name;
};

typedef vector<Var> VarVec;

class VarComp {
public:
  bool operator()(const Var & v1, const Var & v2) {
    return v1.index() < v2.index();
  }
};
typedef set<Var, VarComp> VarSet;
typedef set<Minisat::Lit> LitSet;

// A simple wrapper around an AIGER-specified invariance benchmark.
// It specifically disallows primed variables beyond those required to
// express the (property-constrained) transition relation and the
// primed error constraint.  Variables are kept aligned with the
// variables of any solver created through newSolver().
class Model {
public:
  // Construct a model from a vector of variables, indices indicating
  // divisions between variable types, constraints, next-state
  // functions, the error, and the AND table, closely reflecting the
  // AIGER format.  Easier to use "modelFromAiger()", below.
  Model(vector<Var> _vars, 
        size_t _inputs, size_t _latches, size_t _reps, 
        LitVec _init, LitVec _constraints, LitVec _nextStateFns, 
        Minisat::Lit _err, AigVec _aig) :
    vars(_vars), 
    inputs(_inputs), latches(_latches), reps(_reps),
    primes(_vars.size()), primesUnlocked(true), aig(_aig),
    init(_init), constraints(_constraints), nextStateFns(_nextStateFns),
    _error(_err), inits(NULL), sslv(NULL)
  {
    // create primed inputs and latches in known region of vars
    for (size_t i = inputs; i < reps; ++i) {
      stringstream ss;
      ss << vars[i].name() << "'";
      vars.push_back(Var(ss.str()));
    }
    // same with primed error
    _primedError = primeLit(_error);
    // same with primed constraints
    for (LitVec::const_iterator i = constraints.begin(); 
         i != constraints.end(); ++i)
      primeLit(*i);
  }
  ~Model();

  // Returns the Var of the given Minisat::Lit.
  const Var & varOfLit(Minisat::Lit lit) const {
    Minisat::Var v = Minisat::var(lit);
    assert ((unsigned) v < vars.size());
    return vars[v];
  }

  // Returns the name of the Minisat::Lit.
  string stringOfLit(Minisat::Lit lit) const {
    stringstream ss;
    if (Minisat::sign(lit)) ss << "~";
    ss << varOfLit(lit).name();
    return ss.str();
  }

  // Returns the primed Var/Minisat::Lit for the given
  // Var/Minisat::Lit.  Once lockPrimes() is called, primeVar() fails
  // (with an assertion violation) if it is asked to create a new
  // variable.
  const Var & primeVar(const Var & v, Minisat::SimpSolver * slv = NULL);
  Minisat::Lit primeLit(Minisat::Lit lit, Minisat::SimpSolver * slv = NULL) {
    const Var & pv = primeVar(varOfLit(lit), slv);
    return pv.lit(Minisat::sign(lit));
  }
  Minisat::Lit unprimeLit(Minisat::Lit lit) {
    size_t i = (size_t) var(lit);
    if (i >= primes && i < primes + reps - inputs)
      return Minisat::mkLit((Minisat::Var) (i - primes + inputs), sign(lit));
    else
      return lit;
  }

  // Once all primed variables have been created, it locks the Model
  // from creating any further ones.  Then Solver::newVar() may be
  // called safely.
  //
  // WARNING: Do not call Solver::newVar() until lockPrimes() has been
  // called.
  void lockPrimes() { primesUnlocked = false; }

  // Minisat::Lits corresponding to true/false.
  Minisat::Lit btrue() const { return Minisat::mkLit(vars[0].var(), true); }
  Minisat::Lit bfalse() const { return Minisat::mkLit(vars[0].var(), false); }

  // Primary inputs.
  VarVec::const_iterator beginInputs() const { 
    return vars.begin()+inputs; 
  }
  VarVec::const_iterator endInputs() const { 
    return vars.begin()+latches; 
  }

  // Latches.
  VarVec::const_iterator beginLatches() const { 
    return vars.begin()+latches; 
  }
  VarVec::const_iterator endLatches() const { 
    return vars.begin()+reps; 
  }

  // Next-state function for given latch.
  Minisat::Lit nextStateFn(const Var & latch) const {
    assert (latch.index() >= latches && latch.index() < reps);
    return nextStateFns[latch.index()-latches];
  }

  // Error and its primed form.
  Minisat::Lit error() const { return _error; }
  Minisat::Lit primedError() const { return _primedError; }

  // Invariant constraints
  const LitVec & invariantConstraints() { return constraints; }

  // Creates a Solver and initializes its variables to maintain
  // alignment with the Model's variables.
  Minisat::Solver * newSolver() const;

  // Loads the TR into the solver.  Also loads the primed error
  // definition such that Model::primedError() need only be asserted
  // to activate it.  Invariant constraints (AIGER 1.9) and the
  // negation of the error are always added --- except that the primed
  // form of the invariant constraints are not asserted if
  // !primeConstraints.
  void loadTransitionRelation(Minisat::Solver & slv, 
                              bool primeConstraints = true);
  // Loads the initial condition into the solver.
  void loadInitialCondition(Minisat::Solver & slv) const;
  // Loads the error into the solver, which is only necessary for the
  // 0-step base case of IC3.
  void loadError(Minisat::Solver & slv) const;

  // Use this method to allow the Model to decide how best to decide
  // if a cube has an initial state.
  bool isInitial(const LitVec & latches);

private:
  VarVec vars;
  const size_t inputs, latches, reps, primes;

  bool primesUnlocked;
  typedef unordered_map<size_t, size_t> IndexMap;
  IndexMap primedAnds;

  const AigVec aig;
  const LitVec init, constraints, nextStateFns;
  const Minisat::Lit _error;
  Minisat::Lit _primedError;

  typedef size_t TRMapKey;
  typedef unordered_map<TRMapKey, Minisat::SimpSolver *> TRMap;
  TRMap trmap;

  Minisat::Solver * inits;
  LitSet initLits;

  Minisat::SimpSolver * sslv;

};

// The easiest way to create a model.
Model * modelFromAiger(aiger * aig, unsigned int propertyIndex);

#endif
