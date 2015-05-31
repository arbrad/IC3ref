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

#include <algorithm>
#include <iostream>
#include <set>
#include <sys/times.h>

#include "IC3.h"
#include "Solver.h"
#include "Vec.h"

// A reference implementation of IC3, i.e., one that is meant to be
// read and used as a starting point for tuning, extending, and
// experimenting.
//
// High-level details:
//
//  o The overall structure described in
//
//      Aaron R. Bradley, "SAT-Based Model Checking without
//      Unrolling," VMCAI'11
//
//    including frames, a priority queue of frame-specific proof
//    obligations, and induction-based generalization.  See check(),
//    strengthen(), handleObligations(), mic(), propagate().
//
//  o Lifting, inspired by
//
//      Niklas Een, Alan Mishchenko, Robert Brayton, "Efficient
//      Implementation of Property Directed Reachability," FMCAD'11
//
//    Each CTI is lifted to a larger cube whose states all have the
//    same successor.  The implementation is based on
//
//      H. Chockler, A. Ivrii, A. Matsliah, S. Moran, and Z. Nevo,
//      "Incremental Formal Veriﬁcation of Hardware," FMCAD'11.
//
//    In particular, if s with inputs i is a predecessor of t, then s
//    & i & T & ~t' is unsatisfiable, where T is the transition
//    relation.  The unsat core reveals a suitable lifting of s.  See
//    stateOf().
//
//  o One solver per frame, which various authors of IC3
//    implementations have tried (including me in pre-publication
//    work, at which time I thought that moving to one solver was
//    better).
//
//  o A straightforward proof obligation scheme, inspired by the ABC
//    implementation.  I have so far favored generalizing relative to
//    the maximum possible level in order to avoid over-strengthening,
//    but doing so requires a more complicated generalization scheme.
//    Experiments by Zyad Hassan indicate that generalizing relative
//    to earlier levels works about as well.  Because literals seem to
//    be dropped more quickly, an implementation of the "up" algorithm
//    (described in my FMCAD'07 paper) is unnecessary.
//
//    The scheme is as follows.  For obligation <s, i>:
//
//    1. Check consecution of ~s relative to i-1.
//
//    2. If it succeeds, generalize, then push foward to, say, j.  If
//       j <= k (the frontier), enqueue obligation <s, j>.
//
//    3. If it fails, extract the predecessor t (using stateOf()) and
//       enqueue obligation <t, i-1>.
//
//    The upshot for this reference implementation is that it is
//    short, simple, and effective.  See handleObligations() and
//    generalize().
//
//  o The generalization method described in
//
//      Zyad Hassan, Aaron R. Bradley, and Fabio Somenzi, "Better
//      Generalization in IC3," (submitted May 2013)
//
//    which seems to be superior to the single-clause method described
//    in the original paper, first described in
//
//      Aaron R. Bradley and Zohar Manna, "Checking Safety by
//      Inductive Generalization of Counterexamples to Induction,"
//      FMCAD'07
//
//    The main idea is to address not only CTIs, which are states
//    discovered through IC3's explict backward search, but also
//    counterexamples to generalization (CTGs), which are states that
//    are counterexamples to induction during generalization.  See
//    mic() and ctgDown().
//
//    A basic one-cube generalization scheme can be used instead
//    (third argument of check()).
//
// Limitations in roughly descending order of significance:
//
//  o A permanent limitation is that there is absolutely no
//    simplification of the AIGER spec.  Use, e.g.,
//
//      iimc -t pp -t print_aiger 
//
//    or ABC's simplification methods to produce preprocessed AIGER
//    benchmarks.  This implementation is intentionally being kept
//    small and simple.
//
//  o An implementation of "up" is not provided, as it seems that it's
//    unnecessary when both lifting-based and unsat core-based
//    reduction are applied to a state, followed by mic before
//    pushing.  The resulting cube is sufficiently small.

namespace IC3 {

  class IC3 {
  public:
    IC3(Model & _model) :
      verbose(0), random(false), model(_model), k(1), nextState(0),
      litOrder(), slimLitOrder(),
      numLits(0), numUpdates(0), maxDepth(1), maxCTGs(3),
      maxJoins(1<<20), micAttempts(3), cexState(0), nQuery(0), nCTI(0), nCTG(0),
      nmic(0), satTime(0), nCoreReduced(0), nAbortJoin(0), nAbortMic(0)
    {
      slimLitOrder.heuristicLitOrder = &litOrder;

      // construct lifting solver
      lifts = model.newSolver();
      // don't assert primed invariant constraints
      model.loadTransitionRelation(*lifts, false);
      // assert notInvConstraints (in stateOf) when lifting
      notInvConstraints = Minisat::mkLit(lifts->newVar());
      Minisat::vec<Minisat::Lit> cls;
      cls.push(~notInvConstraints);
      for (LitVec::const_iterator i = model.invariantConstraints().begin();
           i != model.invariantConstraints().end(); ++i)
        cls.push(model.primeLit(~*i));
      lifts->addClause_(cls);
    }
    ~IC3() {
      for (vector<Frame>::const_iterator i = frames.begin(); 
           i != frames.end(); ++i)
        if (i->consecution) delete i->consecution;
      delete lifts;
    }

    // The main loop.
    bool check() {
      startTime = time();  // stats
      while (true) {
        if (verbose > 1) cout << "Level " << k << endl;
        extend();                         // push frontier frame
        if (!strengthen()) return false;  // strengthen to remove bad successors
        if (propagate()) return true;     // propagate clauses; check for proof
        printStats();
        ++k;                              // increment frontier
      }
    }

    // Follows and prints chain of states from cexState forward.
   void printWitness() {
      if (cexState != 0) {
        size_t curr = cexState;
        while (curr) {
          cout << stringOfLitVec(state(curr).inputs) 
               << stringOfLitVec(state(curr).latches) << endl;
          curr = state(curr).successor;
        }
      }
    }

  private:

    int verbose; // 0: silent, 1: stats, 2: all
    bool random;

    string stringOfLitVec(const LitVec & vec) {
      stringstream ss;
      for (LitVec::const_iterator i = vec.begin(); i != vec.end(); ++i)
        ss << model.stringOfLit(*i) << " ";
      return ss.str();
    }

    Model & model;
    size_t k;

    // The State structures are for tracking trees of (lifted) CTIs.
    // Because States are created frequently, I want to avoid dynamic
    // memory management; instead their (de)allocation is handled via
    // a vector-based pool.
    struct State {
      size_t successor;  // successor State
      LitVec latches;
      LitVec inputs;
      size_t index;      // for pool
      bool used;         // for pool
    };
    vector<State> states;
    size_t nextState;
    // WARNING: do not keep reference across newState() calls
    State & state(size_t sti) { return states[sti-1]; }
    size_t newState() {
      if (nextState >= states.size()) {
        states.resize(states.size()+1);
        states.back().index = states.size();
        states.back().used = false;
      }
      size_t ns = nextState;
      assert (!states[ns].used);
      states[ns].used = true;
      while (nextState < states.size() && states[nextState].used)
        nextState++;
      return ns+1;
    }
    void delState(size_t sti) {
      State & st = state(sti);
      st.used = false;
      st.latches.clear();
      st.inputs.clear();
      if (nextState > st.index-1) nextState = st.index-1;
    }
    void resetStates() {
      for (vector<State>::iterator i = states.begin(); i != states.end(); ++i) {
        i->used = false;
        i->latches.clear();
        i->inputs.clear();
      }
      nextState = 0;
    }

    // A CubeSet is a set of ordered (by integer value) vectors of
    // Minisat::Lits.
    static bool _LitVecComp(const LitVec & v1, const LitVec & v2) {
      if (v1.size() < v2.size()) return true;
      if (v1.size() > v2.size()) return false;
      for (size_t i = 0; i < v1.size(); ++i) {
        if (v1[i] < v2[i]) return true;
        if (v2[i] < v1[i]) return false;
      }
      return false;
    }
    static bool _LitVecEq(const LitVec & v1, const LitVec & v2) {
      if (v1.size() != v2.size()) return false;
      for (size_t i = 0; i < v1.size(); ++i)
        if (v1[i] != v2[i]) return false;
      return true;
    }
    class LitVecComp {
    public:
      bool operator()(const LitVec & v1, const LitVec & v2) {
        return _LitVecComp(v1, v2);
      }
    };
    typedef set<LitVec, LitVecComp> CubeSet;

    // A proof obligation.
    struct Obligation {
      Obligation(size_t st, size_t l, size_t d) :
        state(st), level(l), depth(d) {}
      size_t state;  // Generalize this state...
      size_t level;  // ... relative to this level.
      size_t depth;  // Length of CTI suffix to error.
    };
    class ObligationComp {
    public:
      bool operator()(const Obligation & o1, const Obligation & o2) {
        if (o1.level < o2.level) return true;  // prefer lower levels (required)
        if (o1.level > o2.level) return false;
        if (o1.depth < o2.depth) return true;  // prefer shallower (heuristic)
        if (o1.depth > o2.depth) return false;
        if (o1.state < o2.state) return true;  // canonical final decider
        return false;
      }
    };
    typedef set<Obligation, ObligationComp> PriorityQueue;

    // For IC3's overall frame structure.
    struct Frame {
      size_t k;             // steps from initial state
      CubeSet borderCubes;  // additional cubes in this and previous frames
      Minisat::Solver * consecution;
    };
    vector<Frame> frames;

    Minisat::Solver * lifts;
    Minisat::Lit notInvConstraints;

    // Push a new Frame.
    void extend() {
      while (frames.size() < k+2) {
        frames.resize(frames.size()+1);
        Frame & fr = frames.back();
        fr.k = frames.size()-1;
        fr.consecution = model.newSolver();
        if (random) {
          fr.consecution->random_seed = rand();
          fr.consecution->rnd_init_act = true;
        }
        if (fr.k == 0) model.loadInitialCondition(*fr.consecution);
        model.loadTransitionRelation(*fr.consecution);
      }
    }

    // Structure and methods for imposing priorities on literals
    // through ordering the dropping of literals in mic (drop leftmost
    // literal first) and assumptions to Minisat.  The implemented
    // ordering prefers to keep literals that appear frequently in
    // addCube() calls.
    struct HeuristicLitOrder {
      HeuristicLitOrder() : _mini(1<<20) {}
      vector<float> counts;
      size_t _mini;
      void count(const LitVec & cube) {
        assert (!cube.empty());
        // assumes cube is ordered
        size_t sz = (size_t) Minisat::toInt(Minisat::var(cube.back()));
        if (sz >= counts.size()) counts.resize(sz+1);
        _mini = (size_t) Minisat::toInt(Minisat::var(cube[0]));
        for (LitVec::const_iterator i = cube.begin(); i != cube.end(); ++i)
          counts[(size_t) Minisat::toInt(Minisat::var(*i))] += 1;
      }
      void decay() {
        for (size_t i = _mini; i < counts.size(); ++i)
          counts[i] *= 0.99;
      }
    } litOrder;

    struct SlimLitOrder {
      HeuristicLitOrder *heuristicLitOrder;

      SlimLitOrder() {}

      bool operator()(const Minisat::Lit & l1, const Minisat::Lit & l2) const {
        // l1, l2 must be unprimed
        size_t i2 = (size_t) Minisat::toInt(Minisat::var(l2));
        if (i2 >= heuristicLitOrder->counts.size()) return false;
        size_t i1 = (size_t) Minisat::toInt(Minisat::var(l1));
        if (i1 >= heuristicLitOrder->counts.size()) return true;
        return (heuristicLitOrder->counts[i1] < heuristicLitOrder->counts[i2]);
      }
    } slimLitOrder;

    float numLits, numUpdates;
    void updateLitOrder(const LitVec & cube, size_t level) {
      litOrder.decay();
      numUpdates += 1;
      numLits += cube.size();
      litOrder.count(cube);
    }

    // order according to preference
    void orderCube(LitVec & cube) {
      stable_sort(cube.begin(), cube.end(), slimLitOrder);
    }

    typedef Minisat::vec<Minisat::Lit> MSLitVec;

    // Orders assumptions for Minisat.
    void orderAssumps(MSLitVec & cube, bool rev, int start = 0) {
      stable_sort(cube + start, cube + cube.size(), slimLitOrder);
      if (rev) reverse(cube + start, cube + cube.size());
    }

    // Assumes that last call to fr.consecution->solve() was
    // satisfiable.  Extracts state(s) cube from satisfying
    // assignment.
    size_t stateOf(Frame & fr, size_t succ = 0) {
      // create state
      size_t st = newState();
      state(st).successor = succ;
      MSLitVec assumps;
      assumps.capacity(1 + 2 * (model.endInputs()-model.beginInputs())
                       + (model.endLatches()-model.beginLatches()));
      Minisat::Lit act = Minisat::mkLit(lifts->newVar());  // activation literal
      assumps.push(act);
      Minisat::vec<Minisat::Lit> cls;
      cls.push(~act);
      cls.push(notInvConstraints);  // successor must satisfy inv. constraint
      if (succ == 0)
        cls.push(~model.primedError());
      else
        for (LitVec::const_iterator i = state(succ).latches.begin(); 
             i != state(succ).latches.end(); ++i)
          cls.push(model.primeLit(~*i));
      lifts->addClause_(cls);
      // extract and assert primary inputs
      for (VarVec::const_iterator i = model.beginInputs(); 
           i != model.endInputs(); ++i) {
        Minisat::lbool val = fr.consecution->modelValue(i->var());
        if (val != Minisat::l_Undef) {
          Minisat::Lit pi = i->lit(val == Minisat::l_False);
          state(st).inputs.push_back(pi);  // record full inputs
          assumps.push(pi);
        }
      }
      // some properties include inputs, so assert primed inputs after        
      for (VarVec::const_iterator i = model.beginInputs(); 
           i != model.endInputs(); ++i) {
        Minisat::lbool pval = 
          fr.consecution->modelValue(model.primeVar(*i).var());
        if (pval != Minisat::l_Undef)
          assumps.push(model.primeLit(i->lit(pval == Minisat::l_False)));
      }
      int sz = assumps.size();
      // extract and assert latches
      LitVec latches;
      for (VarVec::const_iterator i = model.beginLatches(); 
           i != model.endLatches(); ++i) {
        Minisat::lbool val = fr.consecution->modelValue(i->var());
        if (val != Minisat::l_Undef) {
          Minisat::Lit la = i->lit(val == Minisat::l_False);
          latches.push_back(la);
          assumps.push(la);
        }
      }
      orderAssumps(assumps, false, sz);  // empirically found to be best choice
      // State s, inputs i, transition relation T, successor t:
      //   s & i & T & ~t' is unsat
      // Core assumptions reveal a lifting of s.
      ++nQuery; startTimer();  // stats
      bool rv = lifts->solve(assumps);
      endTimer(satTime);
      assert (!rv);
      // obtain lifted latch set from unsat core
      for (LitVec::const_iterator i = latches.begin(); i != latches.end(); ++i)
        if (lifts->conflict.has(~*i))
          state(st).latches.push_back(*i);  // record lifted latches
      // deactivate negation of successor
      lifts->releaseVar(~act);
      return st;
    }

    // Checks if cube contains any initial states.
    bool initiation(const LitVec & latches) {
      return !model.isInitial(latches);
    }

    // Check if ~latches is inductive relative to frame fi.  If it's
    // inductive and core is provided, extracts the unsat core.  If
    // it's not inductive and pred is provided, extracts
    // predecessor(s).
    bool consecution(size_t fi, const LitVec & latches, size_t succ = 0,
                     LitVec * core = NULL, size_t * pred = NULL, 
                     bool orderedCore = false)
    {
      Frame & fr = frames[fi];
      MSLitVec assumps, cls;
      assumps.capacity(1 + latches.size());
      cls.capacity(1 + latches.size());
      Minisat::Lit act = Minisat::mkLit(fr.consecution->newVar());
      assumps.push(act);
      cls.push(~act);
      for (LitVec::const_iterator i = latches.begin(); 
           i != latches.end(); ++i) {
        cls.push(~*i);
        assumps.push(*i);  // push unprimed...
      }
      // ... order... (empirically found to best choice)
      if (pred) orderAssumps(assumps, false, 1);
      else orderAssumps(assumps, orderedCore, 1);
      // ... now prime
      for (int i = 1; i < assumps.size(); ++i)
        assumps[i] = model.primeLit(assumps[i]);
      fr.consecution->addClause_(cls);
      // F_fi & ~latches & T & latches'
      ++nQuery; startTimer();  // stats
      bool rv = fr.consecution->solve(assumps);
      endTimer(satTime);
      if (rv) {
        // fails: extract predecessor(s)
        if (pred) *pred = stateOf(fr, succ);
        fr.consecution->releaseVar(~act);
        return false;
      }
      // succeeds
      if (core) {
        if (pred && orderedCore) {
          // redo with correctly ordered assumps
          reverse(assumps+1, assumps+assumps.size());
          ++nQuery; startTimer();  // stats
          rv = fr.consecution->solve(assumps);
          assert (!rv);
          endTimer(satTime);
        }
        for (LitVec::const_iterator i = latches.begin(); 
             i != latches.end(); ++i)
          if (fr.consecution->conflict.has(~model.primeLit(*i)))
            core->push_back(*i);
        if (!initiation(*core))
          *core = latches;
      }
      fr.consecution->releaseVar(~act);
      return true;
    }

    size_t maxDepth, maxCTGs, maxJoins, micAttempts;

    // Based on
    //
    //   Zyad Hassan, Aaron R. Bradley, and Fabio Somenzi, "Better
    //   Generalization in IC3," (submitted May 2013)
    //
    // Improves upon "down" from the original paper (and the FMCAD'07
    // paper) by handling CTGs.
    bool ctgDown(size_t level, LitVec & cube, size_t keepTo, size_t recDepth) {
      size_t ctgs = 0, joins = 0;
      while (true) {
        // induction check
        if (!initiation(cube))
          return false;
        if (recDepth > maxDepth) {
          // quick check if recursion depth is exceeded
          LitVec core;
          bool rv = consecution(level, cube, 0, &core, NULL, true);
          if (rv && core.size() < cube.size()) {
            ++nCoreReduced;  // stats
            cube = core;
          }
          return rv;
        }
        // prepare to obtain CTG
        size_t cubeState = newState();
        state(cubeState).successor = 0;
        state(cubeState).latches = cube;
        size_t ctg;
        LitVec core;
        if (consecution(level, cube, cubeState, &core, &ctg, true)) {
          if (core.size() < cube.size()) {
            ++nCoreReduced;  // stats
            cube = core;
          }
          // inductive, so clean up
          delState(cubeState);
          return true;
        }
        // not inductive, address interfering CTG
        LitVec ctgCore;
        bool ret = false;
        if (ctgs < maxCTGs && level > 1 && initiation(state(ctg).latches)
            && consecution(level-1, state(ctg).latches, cubeState, &ctgCore)) {
          // CTG is inductive relative to level-1; push forward and generalize
          ++nCTG;  // stats
          ++ctgs;
          size_t j = level;
          // QUERY: generalize then push or vice versa?
          while (j <= k && consecution(j, ctgCore)) ++j;
          mic(j-1, ctgCore, recDepth+1);
          addCube(j, ctgCore);
        }
        else if (joins < maxJoins) {
          // ran out of CTG attempts, so join instead
          ctgs = 0;
          ++joins;
          LitVec tmp;
          for (size_t i = 0; i < cube.size(); ++i)
            if (binary_search(state(ctg).latches.begin(), 
                              state(ctg).latches.end(), cube[i]))
              tmp.push_back(cube[i]);
            else if (i < keepTo) {
              // previously failed when this literal was dropped
              ++nAbortJoin;  // stats
              ret = true;
              break;
            }
          cube = tmp;  // enlarged cube
        }
        else
          ret = true;
        // clean up
        delState(cubeState);
        delState(ctg);
        if (ret) return false;
      }
    }

    // Extracts minimal inductive (relative to level) subclause from
    // ~cube --- at least that's where the name comes from.  With
    // ctgDown, it's not quite a MIC anymore, but what's returned is
    // inductive relative to the possibly modifed level.
    void mic(size_t level, LitVec & cube, size_t recDepth) {
      ++nmic;  // stats
      // try dropping each literal in turn
      size_t attempts = micAttempts;
      orderCube(cube);
      for (size_t i = 0; i < cube.size();) {
        LitVec cp(cube.begin(), cube.begin() + i);
        cp.insert(cp.end(), cube.begin() + i+1, cube.end());
        if (ctgDown(level, cp, i, recDepth)) {
          // maintain original order
          LitSet lits(cp.begin(), cp.end());
          LitVec tmp;
          for (LitVec::const_iterator j = cube.begin(); j != cube.end(); ++j)
            if (lits.find(*j) != lits.end())
              tmp.push_back(*j);
          cube.swap(tmp);
          // reset attempts
          attempts = micAttempts;
        }
        else {
          if (!--attempts) {
            // Limit number of attempts: if micAttempts literals in a
            // row cannot be dropped, conclude that the cube is just
            // about minimal.  Definitely improves mics/second to use
            // a low micAttempts, but does it improve overall
            // performance?
            ++nAbortMic;  // stats
            return;
          }
          ++i;
        }
      }
    }

    // wrapper to start inductive generalization
    void mic(size_t level, LitVec & cube) {
      mic(level, cube, 1);
    }

    size_t earliest;  // track earliest modified level in a major iteration

    // Adds cube to frames at and below level, unless !toAll, in which
    // case only to level.
    void addCube(size_t level, LitVec & cube, bool toAll = true, 
                 bool silent = false)
    {
      sort(cube.begin(), cube.end());
      pair<CubeSet::iterator, bool> rv = frames[level].borderCubes.insert(cube);
      if (!rv.second) return;
      if (!silent && verbose > 1) 
        cout << level << ": " << stringOfLitVec(cube) << endl;
      earliest = min(earliest, level);
      MSLitVec cls;
      cls.capacity(cube.size());
      for (LitVec::const_iterator i = cube.begin(); i != cube.end(); ++i)
        cls.push(~*i);
      for (size_t i = toAll ? 1 : level; i <= level; ++i)
        frames[i].consecution->addClause(cls);
      if (toAll && !silent) updateLitOrder(cube, level);
    }

    // ~cube was found to be inductive relative to level; now see if
    // we can do better.
    size_t generalize(size_t level, LitVec cube) {
      // generalize
      mic(level, cube);
      // push
      do { ++level; } while (level <= k && consecution(level, cube));
      addCube(level, cube);
      return level;
    }

    size_t cexState;  // beginning of counterexample trace

    // Process obligations according to priority.
    bool handleObligations(PriorityQueue obls) {
      while (!obls.empty()) {
        PriorityQueue::iterator obli = obls.begin();
        Obligation obl = *obli;
        LitVec core;
        size_t predi;
        // Is the obligation fulfilled?
        if (consecution(obl.level, state(obl.state).latches, obl.state, 
                        &core, &predi)) {
          // Yes, so generalize and possibly produce a new obligation
          // at a higher level.
          obls.erase(obli);
          size_t n = generalize(obl.level, core);
          if (n <= k)
            obls.insert(Obligation(obl.state, n, obl.depth));
        }
        else if (obl.level == 0) {
          // No, in fact an initial state is a predecessor.
          cexState = predi;
          return false;
        }
        else {
          ++nCTI;  // stats
          // No, so focus on predecessor.
          obls.insert(Obligation(predi, obl.level-1, obl.depth+1));
        }
      }
      return true;
    }

    bool trivial;  // indicates whether strengthening was required
                   // during major iteration

    // Strengthens frontier to remove error successors.
    bool strengthen() {
      Frame & frontier = frames[k];
      trivial = true;  // whether any cubes are generated
      earliest = k+1;  // earliest frame with enlarged borderCubes
      while (true) {
        ++nQuery; startTimer();  // stats
        bool rv = frontier.consecution->solve(model.primedError());
        endTimer(satTime);
        if (!rv) return true;
        // handle CTI with error successor
        ++nCTI;  // stats
        trivial = false;
        PriorityQueue pq;
        // enqueue main obligation and handle
        pq.insert(Obligation(stateOf(frontier), k-1, 1));
        if (!handleObligations(pq))
          return false;
        // finished with States for this iteration, so clean up
        resetStates();
      }
    }

    // Propagates clauses forward using induction.  If any frame has
    // all of its clauses propagated forward, then two frames' clause
    // sets agree; hence those clause sets are inductive
    // strengthenings of the property.  See the four invariants of IC3
    // in the original paper.
    bool propagate() {
      if (verbose > 1) cout << "propagate" << endl;
      // 1. clean up: remove c in frame i if c appears in frame j when i < j
      CubeSet all;
      for (size_t i = k+1; i >= earliest; --i) {
        Frame & fr = frames[i];
        CubeSet rem, nall;
        set_difference(fr.borderCubes.begin(), fr.borderCubes.end(),
                       all.begin(), all.end(),
                       inserter(rem, rem.end()), LitVecComp());
        if (verbose > 1)
          cout << i << " " << fr.borderCubes.size() << " " << rem.size() << " ";
        fr.borderCubes.swap(rem);
        set_union(rem.begin(), rem.end(),
                  all.begin(), all.end(), 
                  inserter(nall, nall.end()), LitVecComp());
        all.swap(nall);
        for (CubeSet::const_iterator i = fr.borderCubes.begin(); 
             i != fr.borderCubes.end(); ++i)
          assert (all.find(*i) != all.end());
        if (verbose > 1)
          cout << all.size() << endl;
      }
      // 2. check if each c in frame i can be pushed to frame j
      for (size_t i = trivial ? k : 1; i <= k; ++i) {
        int ckeep = 0, cprop = 0, cdrop = 0;
        Frame & fr = frames[i];
        for (CubeSet::iterator j = fr.borderCubes.begin(); 
             j != fr.borderCubes.end();) {
          LitVec core;
          if (consecution(i, *j, 0, &core)) {
            ++cprop;
            // only add to frame i+1 unless the core is reduced
            addCube(i+1, core, core.size() < j->size(), true);
            CubeSet::iterator tmp = j;
            ++j;
            fr.borderCubes.erase(tmp);
          }
          else {
            ++ckeep;
            ++j;
          }
        }
        if (verbose > 1)
          cout << i << " " << ckeep << " " << cprop << " " << cdrop << endl;
        if (fr.borderCubes.empty())
          return true;
      }
      // 3. simplify frames
      for (size_t i = trivial ? k : 1; i <= k+1; ++i)
        frames[i].consecution->simplify();
      lifts->simplify();
      return false;
    }

    int nQuery, nCTI, nCTG, nmic;
    clock_t startTime, satTime;
    int nCoreReduced, nAbortJoin, nAbortMic;
    clock_t time() {
      struct tms t;
      times(&t);
      return t.tms_utime;
    }
    clock_t timer;
    void startTimer() { timer = time(); }
    void endTimer(clock_t & t) { t += (time() - timer); }
    void printStats() {
      if (!verbose) return;
      clock_t etime = time();
      cout << ". Elapsed time: " << ((double) etime / sysconf(_SC_CLK_TCK)) << endl;
      etime -= startTime;
      if (!etime) etime = 1;
      cout << ". % SAT:        " << (int) (100 * (((double) satTime) / ((double) etime))) << endl;
      cout << ". K:            " << k << endl;
      cout << ". # Queries:    " << nQuery << endl;
      cout << ". # CTIs:       " << nCTI << endl;
      cout << ". # CTGs:       " << nCTG << endl;
      cout << ". # mic calls:  " << nmic << endl;
      cout << ". Queries/sec:  " << (int) (((double) nQuery) / ((double) etime) * sysconf(_SC_CLK_TCK)) << endl;
      cout << ". Mics/sec:     " << (int) (((double) nmic) / ((double) etime) * sysconf(_SC_CLK_TCK)) << endl;
      cout << ". # Red. cores: " << nCoreReduced << endl;
      cout << ". # Int. joins: " << nAbortJoin << endl;
      cout << ". # Int. mics:  " << nAbortMic << endl;
      if (numUpdates) cout << ". Avg lits/cls: " << numLits / numUpdates << endl;
    }

    friend bool check(Model &, int, bool, bool);

  };

  // IC3 does not check for 0-step and 1-step reachability, so do it
  // separately.
  bool baseCases(Model & model) {
    Minisat::Solver * base0 = model.newSolver();
    model.loadInitialCondition(*base0);
    model.loadError(*base0);
    bool rv = base0->solve(model.error());
    delete base0;
    if (rv) return false;

    Minisat::Solver * base1 = model.newSolver();
    model.loadInitialCondition(*base1);
    model.loadTransitionRelation(*base1);
    rv = base1->solve(model.primedError());
    delete base1;
    if (rv) return false;

    model.lockPrimes();

    return true;
  }

  // External function to make the magic happen.
  bool check(Model & model, int verbose, bool basic, bool random) {
    if (!baseCases(model))
      return false;
    IC3 ic3(model);
    ic3.verbose = verbose;
    if (basic) {
      ic3.maxDepth = 0;
      ic3.maxJoins = 0;
      ic3.maxCTGs = 0;
    }
    if (random) ic3.random = true;
    bool rv = ic3.check();
    if (!rv && verbose > 1) ic3.printWitness();
    if (verbose) ic3.printStats();
    return rv;
  }

}
