/*****************************************************************************/
/*!
 *\file queryresult.h
 *\brief enumerated type for result of queries
 *
 * Author: Clark Barrett
 *
 * Created: Thu May 18 12:36:25 2006
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 */
/*****************************************************************************/

#ifndef _cvc3__include__queryresult_h_
#define _cvc3__include__queryresult_h_

#include <string>

namespace CVC3 {

/*****************************************************************************/
/*
 * Type for result of queries.  VALID and UNSATISFIABLE are treated as
 * equivalent, as are SATISFIABLE and INVALID.
 */
/*****************************************************************************/
typedef enum QueryResult {
  SATISFIABLE = 0,
  INVALID = 0,
  VALID = 1,
  UNSATISFIABLE = 1,
  ABORT,
  UNKNOWN
} QueryResult;

// Convert a QueryResult to its corresponding string representation
inline std::string QueryResultToString(QueryResult query_result) {
  switch (query_result) {
    case INVALID:
      return "INVALID";
    case VALID:
      return "VALID";
    case ABORT:
      return "ABORT";
    case UNKNOWN:
      return "UNKNOWN";
    default:
      return "(none)";
  }
}

}

#endif
