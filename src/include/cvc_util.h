/*****************************************************************************/
/*!
 *\file cvc_util.h
 *\brief basic helper utilities
 *
 * Author: Clark Barrett
 *
 * Created: Thu Dec  1 16:35:52 2005
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

#ifndef _cvc3__debug_h
#include "debug.h"
#endif

#ifndef _cvc3__cvc_util_h
#define _cvc3__cvc_util_h

namespace CVC3 {

inline std::string to_upper(const std::string & src){
  std::string nameup; 
  for(std::string::const_iterator i=src.begin(), iend = src.end(); i!=iend ; i++){
    nameup.push_back(toupper(*i));
  }
  return nameup;
}

inline std::string to_lower(const std::string & src){
  std::string nameup; 
  for(std::string::const_iterator i=src.begin(), iend = src.end(); i!=iend ; i++){
    nameup.push_back(tolower(*i));
  }
  return nameup;
}

inline std::string int2string(int n) {
  std::ostringstream ss;
  ss << n;
  return ss.str();
}

template<class T>
T abs(T t) { return t < 0 ? -t : t; }

template<class T>
T max(T a, T b) { return a > b ? a : b; }

struct ltstr{
  bool operator()(const std::string& s1, const std::string& s2) const{
    return s1.compare(s2) < 0;
  }
};

template<class T>
class StrPairLess {
public:
  bool operator()(const std::pair<std::string,T>& p1,
		  const std::pair<std::string,T>& p2) const {
    return p1.first < p2.first;
  }
};

template<class T>
std::pair<std::string,T> strPair(const std::string& f, const T& t) {
  return std::pair<std::string,T>(f, t);
}

typedef std::pair<std::string,std::string> StrPair;

//! Sort two vectors based on the first vector
template<class T>
void sort2(std::vector<std::string>& keys, std::vector<T>& vals) {
  DebugAssert(keys.size()==vals.size(), "sort2()");
  // Create std::vector of pairs
  std::vector<std::pair<std::string,T> > pairs;
  for(size_t i=0, iend=keys.size(); i<iend; ++i)
    pairs.push_back(strPair(keys[i], vals[i]));
  // Sort pairs
  StrPairLess<T> comp;
  sort(pairs.begin(), pairs.end(), comp);
  DebugAssert(pairs.size() == keys.size(), "sort2()");
  // Split the pairs back into the original vectors
  for(size_t i=0, iend=pairs.size(); i<iend; ++i) {
    keys[i] = pairs[i].first;
    vals[i] = pairs[i].second;
  }
}

}

#endif
