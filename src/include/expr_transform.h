/*****************************************************************************/
/*!
 *\file expr_transform.h
 *\brief Generally Useful Expression Transformations
 *
 * Author: Clark Barrett
 *
 * Created: Fri Aug  5 16:11:51 2005
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 * 
 */
/*****************************************************************************/

#ifndef _cvc3__include__expr_transform_h_
#define _cvc3__include__expr_transform_h_

#include "expr.h"

namespace CVC3 {

  class VCL;
  class TheoryCore;
  class CommonProofRules;
  class CoreProofRules;

class ExprTransform {

  TheoryCore* d_core;
  CommonProofRules* d_commonRules;
  CoreProofRules* d_rules;

  //! Cache for pushNegation()
  ExprMap<Theorem> d_pushNegCache;

public:
  ExprTransform(TheoryCore* core);
  ~ExprTransform() {}

  //! Simplification that avoids stack overflow
  /*! Stack overflow is avoided by traversing the expression to depths that are
    multiples of 5000 until the bottom is reached.  Then, simplification is done
    bottom-up.
   */
  Theorem smartSimplify(const Expr& e, ExprMap<bool>& cache);
  Theorem preprocess(const Expr& e);
  Theorem preprocess(const Theorem& thm);
  //! Push all negations down to the leaves
  Theorem pushNegation(const Expr& e);
  //! Auxiliary recursive function for pushNegation().
  Theorem pushNegationRec(const Expr& e, bool neg);
  //! Its version for transitivity
  Theorem pushNegationRec(const Theorem& e, bool neg);
  //! Push negation one level down.  Takes 'e' which is 'NOT e[0]'
  Theorem pushNegation1(const Expr& e);
  /*@}*/ // end of preprocessor stuff

};

}

#endif
