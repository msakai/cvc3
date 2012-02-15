/***********************************************************************************[SolverTypes.h]
MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef _cvc3__minisat__types_h_
#define _cvc3__minisat__types_h_

//=================================================================================================
// Variables, literals, clause IDs:

#include "minisat_global.h"
#include <vector>

namespace MiniSat {

  // NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
  // so that they can be used as array indices.
  // CVC additionally requires that N >= 2.
  typedef int Var;
  const int var_Undef = -1;


  class Lit {
    int     x;

    explicit Lit(int index) : x(index) {}   // (lit_Undef)
  public:
    Lit() : x(2*var_Undef) {}   // (lit_Undef)
    explicit Lit(Var var, bool sgn) : x((var+var) + (int)sgn) {}
    Lit operator~ () const { return Lit(x ^ 1); };

    bool sign  () const { return x & 1; };
    int  var   () const { return x >> 1; };
    int  index () const { return x; };
    static Lit  toLit (int i) { return Lit(i); };
    Lit  unsign() const { return Lit(x & ~1); };
    static Lit  id  (Lit p, bool sgn) { return Lit(p.x ^ (int)sgn); };

    bool operator == (const Lit q) const { return index() == q.index(); };
    bool operator != (const Lit q) const { return !(operator==(q)); };
    // '<' guarantees that p, ~p are adjacent in the ordering.;
    bool operator <  (const Lit q) const { return index() < q.index(); }

    uint hash() const { return (uint)x; }

    std::string toString() const {
      std::ostringstream buffer;
      if (sign())
	buffer << "+";
      else
	buffer << "-";
      buffer << var();
      return buffer.str();
    }

    int toDimacs() const { return sign() ? -var() - 1 : var() + 1; }
  };

  const Lit lit_Undef(var_Undef, false);  // }- Useful special constants.
  const Lit lit_Error(var_Undef, true );  // }



  // Clause -- a simple class for representing a clause:
  class Clause {
    uint    size_learnt;
    Lit     data[1];

    static Clause* s_decision;
    static Clause* s_theoryImplication;
  public:
    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    // actual layout is:
    // uint size_learnt : learnt in lowest bit, size * 2 in other bits
    // Lit data[size]
    // int id
    // int pushID (lemma only)
    // float activity (lemma only)
    //
    // using the hand-made allocator allows to allocate the data[]
    // like a static array within clause instead of as a pointer to the array.
    // this shows significant performance improvements
    Clause(bool learnt, const std::vector<Lit>& ps, int id_) {
        size_learnt = (ps.size() << 1) | (int)learnt;
        for (std::vector<Lit>::size_type i = 0; i < ps.size(); i++) data[i] = ps[i];
	id() = id_;
        if (learnt) activity() = 0;
    }

    // -- use this function instead:
    friend Clause* Clause_new(const std::vector<Lit>& ps, int id);
    friend Clause* Lemma_new(const std::vector<Lit>& ps, int id, int pushID);

    int       size        ()      const { return size_learnt >> 1; }
    bool      learnt      ()      const { return size_learnt & 1; }
    Lit       operator [] (int i) const { return data[i]; }
    Lit&      operator [] (int i)       { return data[i]; }
    // intended to be unique id per clause, > 0, or clauseIDNull
    int&      id          ()      const { return *((int*)&data[size()]); }
    
    // used with Solver::push/pop:
    // this is the highest id of all clauses used in the regression /
    // resolution / creation of this lemma
    int&      pushID      ()      const {
      if (learnt())
	return *((int*)&data[size() + 2]);
      else
	return id();
    }
    float&    activity    ()      const {
      DebugAssert(learnt(), "MiniSat::Types:activity: not a lemma");
      return *((float*)&data[size() + 1]);
    }
    void      toLit       (std::vector<Lit>& literals) const;

    static int ClauseIDNull() { return 0; }

    // special Clause, used to mark that an implication is a decision, id = -1.
    static Clause* Decision();
    // special Clause, used to mark that an implication is a theory implication
    // and that the explanation has not been retrieved yet, id = -2.
    static Clause* TheoryImplication();

    std::string toString() const {
      if (size() == 0) return "";

      std::ostringstream buffer;
      buffer << data[0].toString();
      for (int j = 1; j < size(); ++j) {
	buffer << " " << data[j].toString();
      }
      return buffer.str();
    }
  };

  Clause* Clause_new(const std::vector<Lit>& ps, int id);
  Clause* Lemma_new(const std::vector<Lit>& ps, int id, int pushID);

}



//=================================================================================================
#endif
