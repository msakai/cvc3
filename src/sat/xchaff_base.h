/* =========FOR INTERNAL USE ONLY. NO DISTRIBUTION PLEASE ========== */

/*********************************************************************
 Copyright 2000-2001, Princeton University.  All rights reserved. 
 By using this software the USER indicates that he or she has read, 
 understood and will comply with the following:

 --- Princeton University hereby grants USER nonexclusive permission 
 to use, copy and/or modify this software for internal, noncommercial,
 research purposes only. Any distribution, including commercial sale 
 or license, of this software, copies of the software, its associated 
 documentation and/or modifications of either is strictly prohibited 
 without the prior consent of Princeton University.  Title to copyright
 to this software and its associated documentation shall at all times 
 remain with Princeton University.  Appropriate copyright notice shall 
 be placed on all software copies, and a complete copy of this notice 
 shall be included in all copies of the associated documentation.  
 No right is  granted to use in advertising, publicity or otherwise 
 any trademark,  service mark, or the name of Princeton University. 


 --- This software and any associated documentation is provided "as is" 

 PRINCETON UNIVERSITY MAKES NO REPRESENTATIONS OR WARRANTIES, EXPRESS 
 OR IMPLIED, INCLUDING THOSE OF MERCHANTABILITY OR FITNESS FOR A 
 PARTICULAR PURPOSE, OR THAT  USE OF THE SOFTWARE, MODIFICATIONS, OR 
 ASSOCIATED DOCUMENTATION WILL NOT INFRINGE ANY PATENTS, COPYRIGHTS, 
 TRADEMARKS OR OTHER INTELLECTUAL PROPERTY RIGHTS OF A THIRD PARTY.  

 Princeton University shall not be liable under any circumstances for 
 any direct, indirect, special, incidental, or consequential damages 
 with respect to any claim by USER or any third party on account of 
 or arising from the use, or inability to use, this software or its 
 associated documentation, even if Princeton University has been advised
 of the possibility of those damages.
*********************************************************************/


#ifndef __BASIC_CLASSES__
#define __BASIC_CLASSES__

#include <vector>
#include <iostream>
#include <assert.h>
using namespace std;

typedef enum Unknown {
  UNKNOWN = -1
} Unknown;

#define NULL_CLAUSE  	-1
#define FLIPPED		-2

typedef int ClauseIdx; //used to refer a clause. Because of dynamic 
                       //allocation of vector storage, no pointer is allowered

/**Class**********************************************************************

  Synopsis    [Definition of a literal]

  Description [A literal is a variable with phase. Two thing determing a lteral: 
               it's "sign", and the variable index. One bit is used to mark it's
	       sign. 0->positive, 1->negative.

	       For every clause with literal count larger than 1, there are two
	       special literals which are designated ht_literal (stands for 
	       head/tail literal to imitate SATO) It is specially marked with 2 bits: 
	       00->not ht; dir = 1;  or dir = -1; 10 is not valid.
	       Each literal is represented by a 32 bit integer, with one bit 
	       representing it's phase and 2 bits indicate h/t property.

	       All the literals are collected in a storage space called literal
	       pool. An element in a literal pool can be a literal or special
	       spacing element to indicate the termination of a clause. The 
	       spacing element has negative value of the clause index.]

  SeeAlso     [CDatabase, CClause]

******************************************************************************/

class CLitPoolElement
{
protected:
    int _val;				      
public:
//======constructors & destructors============
    CLitPoolElement(void) {
	_val=0;
    }
    CLitPoolElement(int val):_val(val){}
//=========member access function=============
    int & val(void) { 
	return _val; 
    }
    int s_var(void) { //stands for signed variable, i.e. 2*var_idx + sign
	return _val>>2;
    }
    int var_index(void) {
	return _val>>3; 
    }
    bool var_sign(void) { 
	return ( (_val>> 2)& 0x1); 
    }
    void set (int s_var) {
	_val = (s_var << 2);
    }
    void set(int v, int s) { 
	_val = (((v<<1) + s)<< 2); 
    }
//following are the functions for the special head/tail literals for FAST_BCP
    int direction (void) {
	return ((_val&0x03) - 2);
    }
    bool is_ht(void) {
	return _val&0x03;
    }
    void unset_ht(void) {
	_val = _val & (0x0fffffffc);
    }
    void set_ht(int dir) {
	_val = _val + dir + 2;
    }

    //following are used for spacing (e.g. indicate clause's end)
    bool is_literal(void) {
	return _val > 0;
    }
    void set_clause_index(int cl_idx) {
	_val = - cl_idx;
    }
    int get_clause_index(void) {
	return -_val; 
    }
    //misc functions
    int find_clause_idx(void) {
	CLitPoolElement * ptr;
	for (ptr = this; ptr->is_literal(); ++ ptr);
	return ptr->get_clause_index();
    }
	
    void dump(ostream & os= cout) { 
	os << (var_sign()?" -":" +") << var_index();
	if (is_ht()) os << "*";
    }
    friend ostream & operator << ( ostream & os, CLitPoolElement & l) { 
	l.dump(os); 
	return os;
    }
};

/**Class**********************************************************************

  Synopsis    [Definition of a clause]

  Description [A clause is consisted of a certain number of literals. 
               All literals are collected in a single large vector, we call it
	       literal pool. Each clause has a pointer to the beginning position
	       of it's literals in the pool. The boolean propagation mechanism
	       use two pointers (called head/tail pointer, by sato's convention)
	       which always point to the last assigned literals of this clause.]

  SeeAlso     [CDatabase]

******************************************************************************/
class CClause
{
protected:
    CLitPoolElement * _first_lit;	//pointer to the first literal in literal pool
    int _num_lits;			//number of literals
    bool _in_use;			//indicate if this clause has been deleted or not
public:
//constructors & destructors
    CClause(void){}

    ~CClause() {}
//initialization & clear up
    void init(CLitPoolElement * head, int num_lits) { //initialization of a clause
	_first_lit = head;
	_num_lits = num_lits;
  	_in_use = true;
    }
//member access function
    CLitPoolElement * literals(void) { 		//literals()[i] is it's the i-th literal
	return _first_lit; 
    }	
    CLitPoolElement * & first_lit(void) {	//use it only if you want to modify _first_lit
	return _first_lit; 
    }
    int & num_lits(void) { 
	return _num_lits; 
    }
    bool & in_use(void) { 
	return _in_use; 
    }
    CLitPoolElement & literal(int idx) { 	//return the idx-th literal
	return literals()[idx]; 
    }
//misc functions
    void dump(ostream & os = cout) { 
	if (!in_use()) 
	    os << "\t\t\t======removed=====";
	for (int i=0, sz=num_lits(); i<sz; ++i) 
	    os << literal(i);
	os << endl;
    }
//    friend ostream & operator << (ostream & os, CClause & cl);
    friend ostream & operator << ( ostream & os, CClause & cl) { 
	cl.dump(os); 
	return os;
    }
};


/**Class**********************************************************************

  Synopsis    [Definition of a variable]

  Description [CVariable contains the necessary information for a variable.
               _ht_ptrs are the head/tail literals of this variable (int two phases)]

  SeeAlso     [CDatabase]

******************************************************************************/
class CVariable 
{
protected:
    bool _is_marked		: 1;	//used in conflict analysis.

    int _in_new_cl		: 2;	//it can take 3 value 0: pos phase, 
                                        //1: neg phase, -1 : not in new clause;
                                        //used to keep track of literals appearing
                                        //in newly added clause so that a. each
                                        //variable can only appearing in one phase
                                        //b. same literal won't appear more than once.

    ClauseIdx _antecedence	: 29;   //used in conflict analysis

    short _value;			//can be 1, 0 or UNKNOWN

    short _dlevel; 			//decision level this variable being assigned

    vector<CLitPoolElement *> _ht_ptrs[2];	//literal of this var appearing in h/t. 0: pos, 1: neg

protected:
    int _lits_count[2];
    int _scores[2];		
    int _var_score_pos;
public:
    int & score(int i) { return _scores[i]; }
    int score(void) { return score(0)>score(1)?score(0):score(1); }
    int & var_score_pos(void) { return _var_score_pos; }
public:
//constructors & destructors
    CVariable(void) {
	_value = UNKNOWN; 
	_antecedence=NULL_CLAUSE; 
	_dlevel = -1; 
	_in_new_cl = -1;	
	_is_marked = false;
	_scores[0] = _scores[1] = 0;
	_var_score_pos = _lits_count[0] = _lits_count[1] = 0;
    }
//member access function
    short & value(void) { 
	return _value;
    }
    short & dlevel(void) { 
	return _dlevel;
    }
    int in_new_cl(void) { 
	return _in_new_cl; 
    } 
    void set_in_new_cl(int phase) { 
	_in_new_cl = phase; 
    }
    int & lits_count(int i) {
	return _lits_count[i];
    }

    bool is_marked(void) { 
	return _is_marked; 
    }    
    void set_marked(void) { 
	_is_marked = true; 
    }
    void clear_marked(void) { 
	_is_marked = false; 
    }

    ClauseIdx get_antecedence(void) { 
	return _antecedence; 
    }
    void set_antecedence(ClauseIdx ante) { 
	_antecedence = ante; 
    }

    vector<CLitPoolElement *> & ht_ptr(int i) { return _ht_ptrs[i]; }

//misc functions
    void  dump(ostream & os=cout) {
	if (is_marked()) os << "*" ;
	os << "V: " << _value << "  DL: " << _dlevel 
	   << "  Ante: " << _antecedence << endl;
	for (int j=0; j< 2; ++j) {
	    os << (j==0?"Pos ":"Neg ") <<  "(" ;
	    for (unsigned i=0; i< ht_ptr(j).size(); ++i )
		os << ht_ptr(j)[i]->find_clause_idx() << "  " ;
	    os << ")" << endl;
	}
	os << endl;
    }
//      friend ostream & operator << (ostream & os, CVariable & v);
    friend ostream & operator << ( ostream & os, CVariable & v) { 
	v.dump(os); 
	return os;
    }
};
#endif











