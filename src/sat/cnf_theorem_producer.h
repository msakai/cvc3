/*****************************************************************************/
/*!
 *\file cnf_theorem_producer.h
 *\brief Implementation of CNF_Rules API
 *
 * Author: Clark Barrett
 *
 * Created: Thu Jan  5 05:33:42 2006
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

#ifndef _cvc3__sat__cnf_theorem_producer_h_
#define _cvc3__sat__cnf_theorem_producer_h_

#include "theorem_producer.h"
#include "cnf_rules.h"

namespace CVC3 {

  class CNF_TheoremProducer
    : public CNF_Rules,
      public TheoremProducer {

  public:
    CNF_TheoremProducer(TheoremManager* tm): TheoremProducer(tm) { }
    ~CNF_TheoremProducer() { }

    Theorem learnedClause(const Theorem& thm);
    Theorem ifLiftRule(const Expr& e, int itePos);

  }; // end of class CNF_TheoremProducer
} // end of namespace CVC3
#endif
