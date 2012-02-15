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


#ifndef __DATABASE__
#define __DATABASE__

#include "xchaff_base.h"
#include <queue>

#define STARTUP_LIT_POOL_SIZE 0x1000

struct pair_int_equal {
    bool operator () (pair<int,int> a, pair<int,int> b) {
	return (a.first==b.first && a.second == b.second);
    }
};

struct pair_int_hash_fun {
    size_t operator () (const pair<int, int> a) const {
	return (a.first + (a.second << 16));
    }
};

/**Struct**********************************************************************

  Synopsis    [Definition of the statistics of clause database]

  Description []

  SeeAlso     [CDatabase]

******************************************************************************/

struct CDatabaseStats {
    int mem_used_up_counts;
    bool mem_used_up;
    int init_num_clauses;
    int init_num_literals;
    int num_added_clauses;
    int num_added_literals;
    int num_deleted_clauses;
    int num_deleted_literals;
};

/**Class**********************************************************************

  Synopsis    [Definition of clause database ]

  Description [Clause Database is the place where the information of the 
               SAT problem are stored. it is a parent class of CSolver ]

  SeeAlso     [CSolver]

******************************************************************************/
class CDatabase
{
protected:
    CDatabaseStats _stats;
    //for efficiency, the memeory management of lit pool is done by the solver

    CLitPoolElement * _lit_pool_start;		//the begin of the lit vector
    CLitPoolElement * _lit_pool_finish;		//the tail of the used lit vector
    CLitPoolElement * _lit_pool_end_storage;   	//the storage end of lit vector

    vector<CVariable> _variables; //note: first element is not used
    vector<CClause> _clauses;
    queue<ClauseIdx> _unused_clause_idx_queue;

    int _num_var_in_new_cl;
    int _mem_limit;
public:
//constructors & destructors
    CDatabase() ;
    ~CDatabase() { 
	delete [] _lit_pool_start; 
    }
    void init(void) {
        init_num_clauses() = num_clauses();
	init_num_literals() = num_literals();
    }
//member access function
    vector<CVariable>& variables(void) { 
	return _variables; 
    }
    vector<CClause>& clauses(void) { 
	return _clauses; 
    }
    CVariable & variable(int idx) { 
	return _variables[idx]; 
    }
    CClause & clause(ClauseIdx idx) { 
	return _clauses[idx]; 
    }
    CDatabaseStats & stats(void) {
	return _stats;
    }
    void set_mem_limit(int n) {
	_mem_limit = n;
    }
//some stats
    int & init_num_clauses() { return _stats.init_num_clauses; }
    int & init_num_literals () { return _stats.init_num_literals; }
    int & num_added_clauses () { return _stats.num_added_clauses; }
    int & num_added_literals() { return _stats.num_added_literals; }
    int & num_deleted_clauses() { return _stats.num_deleted_clauses; }
    int & num_deleted_literals() { return _stats.num_deleted_literals; }

//lit pool naming convention is following STL Vector
    CLitPoolElement * lit_pool_begin(void) { 
	return _lit_pool_start; 
    }
    CLitPoolElement * lit_pool_end(void) { 
	return _lit_pool_finish; 
    }
    void lit_pool_push_back(int value) { 
	assert (_lit_pool_finish <= _lit_pool_end_storage );
	_lit_pool_finish->val() = value;
	++ _lit_pool_finish;
    }
    int lit_pool_size(void) { 
	return _lit_pool_finish - _lit_pool_start; 
    }
    int lit_pool_free_space(void) { 
	return _lit_pool_end_storage - _lit_pool_finish; 
    }
    CLitPoolElement & lit_pool(int i) {
	return _lit_pool_start[i];
    }
//functions on lit_pool
    void output_lit_pool_state(void);

    bool enlarge_lit_pool(void);

    void compact_lit_pool(void);

//functions 
    int estimate_mem_usage (void) 
	{
	int lit_pool = sizeof(CLitPoolElement) * 
	               (lit_pool_size() + lit_pool_free_space());
	int mem_vars = sizeof(CVariable) * 
                       variables().capacity();
	int mem_cls = sizeof(CClause) * 
                      clauses().capacity();
	int mem_cls_queue = sizeof(int) * 
                            _unused_clause_idx_queue.size();
	int mem_ht_ptrs =0, mem_lit_clauses = 0;
	mem_ht_ptrs = sizeof(CLitPoolElement*) * 
	                  (clauses().size()-_unused_clause_idx_queue.size()) * 2;
	return (lit_pool + mem_vars + mem_cls +
		mem_cls_queue + mem_ht_ptrs + mem_lit_clauses);
	}
    int mem_usage(void) {
	int lit_pool = (lit_pool_size() + lit_pool_free_space()) * sizeof(CLitPoolElement);
	int mem_vars = sizeof(CVariable) * variables().capacity();
	int mem_cls = sizeof(CClause) * clauses().capacity();
	int mem_cls_queue = sizeof(int) * _unused_clause_idx_queue.size();
	int mem_ht_ptrs = 0, mem_lit_clauses = 0;
	for (unsigned i=0; i< variables().size(); ++i) {
	    CVariable & v = variable(i);
	    mem_ht_ptrs	+= v.ht_ptr(0).capacity() + v.ht_ptr(1).capacity(); 
	}
	mem_ht_ptrs *= sizeof(CLitPoolElement*);
	mem_lit_clauses *= sizeof(ClauseIdx);
	return (lit_pool + mem_vars + mem_cls + 
		mem_cls_queue + mem_ht_ptrs + mem_lit_clauses);
    }
    void set_variable_number(int n) { 
	variables().resize(n + 1) ; 
    }
    int add_variable(void) {
	variables().resize( variables().size() + 1);
	return variables().size() - 1;
    }
    int num_variables(void) {
	return variables().size() - 1;
    }

    int num_clauses(void) { 
	return _clauses.size() - _unused_clause_idx_queue.size(); 
    }
    int num_literals(void) { 
	return _stats.num_added_literals - _stats.num_deleted_literals; 
    }

    void mark_clause_deleted(CClause & cl) {
	++_stats.num_deleted_clauses;
	_stats.num_deleted_literals += cl.num_lits();
	cl.in_use() = false;
	for (int i=0; i< cl.num_lits(); ++i) {
	    CLitPoolElement & l = cl.literal(i);
	    --variable(l.var_index()).lits_count(l.var_sign());
	    l.val() = 0;
	}
    }
    void mark_var_in_new_cl(int v_idx, int phase ) { 
	    if (variable(v_idx).in_new_cl() == -1 && phase != -1)
		++ _num_var_in_new_cl;
	    else if (variable(v_idx).in_new_cl() != -1 && phase == -1)
		-- _num_var_in_new_cl;
	    else assert (0 && "How can this happen? ");
	    variable(v_idx).set_in_new_cl( phase ); 
    }
    int literal_value (CLitPoolElement l) {	//note: it will return 0 or 1 or other , 
	                                         //here "other" may not equal UNKNOWN
	return variable(l.var_index()).value() ^ l.var_sign(); 
    }

    int find_unit_literal(ClauseIdx cl);	//if not unit clause, return 0.

    bool is_conflict(ClauseIdx cl); 		//e.g. all literals assigned value 0

    bool is_satisfied(ClauseIdx cl);		//e.g. at least one literal has value 1

    void detail_dump_cl(ClauseIdx cl_idx, ostream & os = cout);

    void dump(ostream & os = cout);
};

#endif















