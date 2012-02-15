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



#ifndef __SAT_SOLVER__
#define __SAT_SOLVER__

#include <sys/time.h>
#include <sys/resource.h>

#include "xchaff_utils.h"
#include "xchaff_dbase.h"

#ifndef __SAT_STATUS__
#define __SAT_STATUS__
enum SAT_StatusT {
    UNDETERMINED,
    UNSATISFIABLE,
    SATISFIABLE,
    TIME_OUT,
    MEM_OUT,
    ABORTED
};
#endif

enum SAT_DeductionT {
    CONFLICT,
    NO_CONFLICT
};

typedef void(*HookFunPtrT)(void *) ;
/**Struct**********************************************************************

  Synopsis    [Sat solver parameters ]

  Description []

  SeeAlso     []

******************************************************************************/
struct CSolverParameters {
    float 	time_limit;

    int 	decision_strategy;
    int 	preprocess_strategy;

    bool 	allow_clause_deletion;
    int	       	clause_deletion_interval;
    int 	max_unrelevance;
    int 	min_num_clause_lits_for_delete;
    int 	max_conflict_clause_length;
    int		bubble_init_step;

    int		verbosity;
    int 	randomness;

    bool	allow_restart;
    float	next_restart_time;
    float	restart_time_increment;
    float	restart_time_incr_incr;
    int 	next_restart_backtrack;
    int 	restart_backtrack_incr;		
    int		restart_backtrack_incr_incr;
    int		restart_randomness;	
    int		base_randomness;

    bool	back_track_complete;
    int		conflict_analysis_method;
    bool 	allow_multiple_conflict;
    bool 	allow_multiple_conflict_clause;
};
/**Struct**********************************************************************

  Synopsis    [Sat solver statistics ]

  Description []

  SeeAlso     []

******************************************************************************/
struct CSolverStats {
    bool 	is_solver_started;	
    int 	outcome;
    
    bool	is_mem_out;		//this flag will be set if memory out

    long 	start_cpu_time;    	
    long	last_cpu_time;
    long 	finish_cpu_time;
    long 	start_world_time;
    long 	finish_world_time;

    long long 	total_bubble_move;

    int 	num_decisions;
    int		num_backtracks;
    int 	max_dlevel;
    int 	num_implications;
    int 	num_free_variables;
};

/**Class**********************************************************************

  Synopsis    [Sat Solver]

  Description [This class contains the process and datastructrues to solve
               the Sat problem.]

  SeeAlso     []

******************************************************************************/
class CSolver:public CDatabase
{
protected:
    int 			_dlevel;		//current decision elvel
    vector<vector<int> *> 	_assignment_stack;
    queue<pair<int,ClauseIdx> >	_implication_queue;
    CSolverParameters 		_params;
    CSolverStats     		_stats;

    vector<pair<int,pair< HookFunPtrT, int> > > _hooks;

//these are for decision making
    int				_max_score_pos;
    vector<int>			_last_var_lits_count[2];
    vector<pair<int,int> >_var_order;	

//these are for conflict analysis
    int 		_num_marked;	//used when constructing conflict clauses
    vector<ClauseIdx> 	_conflicts;	//the conflict clauses		       
    vector<long> 	_conflict_lits; //used when constructing conflict clauses

//these are for the extended API
    void (*_dlevel_hook)(void *, int);
    int  (*_decision_hook)(void *, bool *);
    void (*_assignment_hook)(void *, int, int);
    void (*_deduction_hook)(void *);
    void *_dlevel_hook_cookie;
    void *_decision_hook_cookie;
    void *_assignment_hook_cookie;
    void *_deduction_hook_cookie;

//needed to support dynamic adding of unit clauses
    vector<ClauseIdx> _addedUnitClauses;

protected:
    void real_solve(void);

    int preprocess(bool allowNewClauses);

    int deduce(void);

    bool decide_next_branch(void);

    int analyze_conflicts(void);
    int conflict_analysis_grasp (void);
    int conflict_analysis_zchaff (void);

    void back_track(int level);

    void init(void);
//for conflict analysis
    void mark_vars_at_level(ClauseIdx cl, 
			    int var_idx, 
			    int dl);

    int find_max_clause_dlevel(ClauseIdx cl);	//the max dlevel of all the assigned lits in this clause

//for bcp 
    void set_var_value(int var, 
		       int value, 
		       ClauseIdx ante, 
		       int dl);
    void set_var_value_not_current_dl(int v, 
				      vector<CLitPoolElement *> & neg_ht_clauses);
    void set_var_value_with_current_dl(int v, 
				       vector<CLitPoolElement*> & neg_ht_clauses);
    void unset_var_value(int var);

    void run_periodic_functions (void);
//misc functions
    void update_var_stats(void);	

    bool time_out(void);

    void delete_unrelevant_clauses(void);
public:
//constructors and destructors
    CSolver() ;
    ~CSolver();
//member access function
    void set_time_limit(float t) 
	{ _params.time_limit = t; }
    void set_mem_limit(int s) 	{ 
	CDatabase::set_mem_limit(s);
    }
    void set_decision_strategy(int s) 
	{ _params.decision_strategy = s; }
    void set_preprocess_strategy(int s) 
	{ _params.preprocess_strategy = s; }
    void enable_cls_deletion(bool allow) 
	{ _params.allow_clause_deletion = allow; }
    void set_cls_del_interval(int n)
	{ _params.clause_deletion_interval = n; }
    void set_max_unrelevance(int n ) 
	{ _params.max_unrelevance = n; }
    void set_min_num_clause_lits_for_delete(int n) 
	{ _params.min_num_clause_lits_for_delete = n; }
    void set_max_conflict_clause_length(int l) 
	{ _params.max_conflict_clause_length = l; }
    void set_allow_multiple_conflict( bool b = false) {
	_params.allow_multiple_conflict = b ;
    }
    void set_allow_multiple_conflict_clause( bool b = false) {
	_params.allow_multiple_conflict_clause = b; 
    }
    void set_randomness(int n) {
	_params.base_randomness = n;
    }
    void set_random_seed(int seed) {
	if (seed < 0)
	    srand ( current_world_time() );
	else 
	    srand (seed);
    }

//these are for the extended API
    void RegisterDLevelHook(void (*f)(void *, int), void *cookie)
         { _dlevel_hook = f; _dlevel_hook_cookie = cookie; }
    void RegisterDecisionHook(int (*f)(void *, bool *), void *cookie)
         { _decision_hook = f; _decision_hook_cookie = cookie; }
    void RegisterAssignmentHook(void (*f)(void *, int, int), void *cookie)
         { _assignment_hook = f; _assignment_hook_cookie = cookie; }
    void RegisterDeductionHook(void (*f)(void *), void *cookie)
         { _deduction_hook = f;
           _deduction_hook_cookie = cookie; }

    int outcome () 	{ return _stats.outcome; }
    int num_decisions() { return _stats.num_decisions; }
    int & num_free_variables() {
	return _stats.num_free_variables;
    }
    int max_dlevel() 	{ return _stats.max_dlevel; }
    int num_implications() { return _stats.num_implications; }
    long long total_bubble_move(void) {	return _stats.total_bubble_move; }

    char * version(void){ 
	return "Z2001.2.17"; 
    }

    int current_cpu_time(void) {
	struct rusage ru;
	getrusage(RUSAGE_SELF, &ru);
	return ( ru.ru_utime.tv_sec*1000 +
		 ru.ru_utime.tv_usec/1000+
		 ru.ru_stime.tv_sec*1000 +
		 ru.ru_stime.tv_usec/1000 );
    }

    int current_world_time(void) {
	struct timeval tv;
	struct timezone tz;
	gettimeofday(&tv,&tz);	
	return (tv.tv_sec * 1000 + tv.tv_usec/1000) ;
    }
    
    float elapsed_cpu_time() {
	int current = current_cpu_time();
	int diff = current - _stats.last_cpu_time;
	_stats.last_cpu_time = current;
	return diff/1000.0;
    }

    float total_run_time() {
      if (!_stats.is_solver_started) return 0;
      return (current_cpu_time() -
	      _stats.start_cpu_time)/1000.0 ;
    }

    float cpu_run_time() { 
	return (_stats.finish_cpu_time - 
		_stats.start_cpu_time)/1000.0 ;
    }

    float world_run_time() { 
	return (_stats.finish_world_time - 
		_stats.start_world_time) / 1000.0 ;
    }

    int estimate_mem_usage() {
	return CDatabase::estimate_mem_usage();
    }
    int mem_usage(void) {
	int mem_dbase = CDatabase::mem_usage();
	int mem_assignment = 0;
	for (int i=0; i< _stats.max_dlevel; ++i)
	    mem_assignment += _assignment_stack[i]->capacity() * sizeof(int);
	mem_assignment += sizeof(vector<int>)* _assignment_stack.size();
	return mem_dbase + mem_assignment;
    }
    int & dlevel() { return _dlevel; }

//top level function
    void add_hook( HookFunPtrT fun, int interval) {
	pair<HookFunPtrT, int> a(fun, interval);
	_hooks.push_back(pair<int, pair<HookFunPtrT, int> > (0, a));
    }

    void queue_implication (int lit, ClauseIdx ante_clause) {
	CHECK (cout << "\t\t\t\t\t\tQueueing " << (lit&0x01?" -":" +") << (lit>>1) ;
	       cout << " because of  " << ante_clause << endl; );
	_implication_queue.push(pair<int, ClauseIdx>(lit, ante_clause));
    }

    int add_variables(int new_vars);

    ClauseIdx add_clause(vector<long>& lits, bool addConflicts=true);

    void verify_integrity(void);

//    ClauseIdx add_clause_with_order_adjustment(int * lits, int n_lits);
    void restart (void){
	if (_params.verbosity > 1 ) 
	    cout << "Restarting ... " << endl;
	if (dlevel() > 1) {
	    //clean up the original var_stats.
	    for (unsigned i=1; i<variables().size(); ++i) {
		variable(i).score(0) = 0;
		variable(i).score(1) = 0;
		_last_var_lits_count[0][i] = 0;
		_last_var_lits_count[1][i] = 0;
	    }
	    update_var_stats();
	    back_track(1); //backtrack to level 0. restart.	
	}
    }
    
    int	solve(bool allowNewClauses);
    int continueCheck();

    void dump_assignment_stack(ostream & os = cout);

    void output_current_stats(void);

    void dump(ostream & os = cout ) {
	CDatabase::dump(os);
	dump_assignment_stack(os);
    }
};
#endif































