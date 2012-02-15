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
 any trademark, service mark, or the name of Princeton University. 


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


#include "xchaff_solver.h"
#include <algorithm>


CSolver::CSolver(void)    
{
    dlevel()=0;
    _params.time_limit 		= 3600 * 48;		//2 days
    _params.decision_strategy 	= 0;
    _params.preprocess_strategy = 0;
    _params.allow_clause_deletion 		= true ;
    _params.clause_deletion_interval		= 5000;
    _params.max_unrelevance			= 20;
    _params.min_num_clause_lits_for_delete	= 100;
    _params.max_conflict_clause_length		= 5000;
    _params.bubble_init_step 	= 32;

    _params.randomness		= 0;
    _params.verbosity		= 0;

    _params.back_track_complete	= true;
    _params.allow_multiple_conflict		= false;
    _params.allow_multiple_conflict_clause	= false;

    _params.allow_restart	= true;	
    _params.next_restart_time	= 50;		//this set the first restart time (in seconds)
    _params.restart_time_increment	= 0;
    _params.restart_time_incr_incr = 0;

    _params.next_restart_backtrack= 0;
    _params.restart_backtrack_incr= 40000;		
    _params.restart_backtrack_incr_incr = 100;

    _params.restart_randomness	= 0;	
    _params.base_randomness	= 0;
    _params.randomness		= 0;

    _stats.is_solver_started	= false;
    _stats.outcome		= UNKNOWN;
    _stats.is_mem_out		= false;
    _stats.start_cpu_time	= 0;	   	
    _stats.finish_cpu_time	= 0;
    _stats.last_cpu_time	= 0;	   	

    _stats.start_world_time	= 0;
    _stats.finish_world_time	= 0;

    _stats.num_decisions 	= 0;
    _stats.num_backtracks	= 0;
    _stats.max_dlevel 		= 0;
    _stats.num_implications   	= 0;

    _num_marked 		= 0;
    _dlevel			= 0;		
    _stats.total_bubble_move 	= 0;

    _dlevel_hook = NULL;
    _decision_hook = NULL;
    _assignment_hook = NULL;
    _deduction_hook = NULL;
}

CSolver::~CSolver()
{
  if (_stats.is_solver_started) {
    for (unsigned i=0; i<variables().size(); ++i)
	delete _assignment_stack[i];
  }
}

void CSolver::run_periodic_functions(void)
{
    //a. clause deletion
    if ( _params.allow_clause_deletion &&
	 _stats.num_backtracks % _params.clause_deletion_interval == 0)
  	    delete_unrelevant_clauses(); 
    //b. restart
    if (_params.allow_restart && _stats.num_backtracks > _params.next_restart_backtrack) {
	_params.next_restart_backtrack += _params.restart_backtrack_incr;
	_params.restart_backtrack_incr += _params.restart_backtrack_incr_incr;
  	float current = current_cpu_time()/1000;
  	if (current > _params.next_restart_time) {
  	    if (_params.verbosity > 1) cout << "restart..." << endl;
  	    _params.next_restart_time = current + _params.restart_time_increment;
	    _params.restart_time_increment += _params.restart_time_incr_incr;
	    _params.randomness = _params.restart_randomness;
	    restart();
	}
    }    
    //c. update var stats for decision
    if ((_stats.num_decisions % 0xff)==0) 
	    update_var_stats();
    //d. run hook functions
    for (unsigned i=0; i< _hooks.size(); ++i) {
	pair<int,pair<HookFunPtrT, int> > & hook = _hooks[i];
	if (_stats.num_decisions >= hook.first) {
	    hook.first += hook.second.second;
	    hook.second.first((void *) this);
	}
    }
} 


void CSolver::init(void)
{
    CDatabase::init();

    _stats.is_solver_started 	= true;
    _stats.start_cpu_time 	= current_cpu_time();
    _stats.start_world_time	= current_world_time();
    _stats.num_free_variables	= num_variables();
    for (unsigned i=0; i<variables().size(); ++i)
	_assignment_stack.push_back(new vector<int>);

    _var_order.resize( num_variables());
    _last_var_lits_count[0].resize(variables().size());
    _last_var_lits_count[1].resize(variables().size());
    CHECK(dump());
}


int CSolver::add_variables(int new_vars)
{
  int old_num_vars = variables().size();
  int num_vars = old_num_vars + new_vars;
  variables().resize(num_vars) ; 
  if (_stats.is_solver_started) {
    _stats.num_free_variables += new_vars;

    for (int i=old_num_vars; i<num_vars; ++i) {
      _assignment_stack.push_back(new vector<int>);
      _var_order.push_back(pair<int, int>(i,0));
    }
    _last_var_lits_count[0].resize(num_vars);
    _last_var_lits_count[1].resize(num_vars);
  }
  return old_num_vars;
}


ClauseIdx CSolver::add_clause(vector<long>& lits, bool addConflicts) {
    int new_cl;
    int n_lits = lits.size();
    //a. do we need to enlarge lits pool?
    while (lit_pool_free_space() <= n_lits + 1) { 
	if (enlarge_lit_pool()==false) 
	    return -1; //mem out, can't enlarge lit pool, because 
	               //ClauseIdx can't be -1, so it shows error.
    }	
    //b. get a free cl index;
    if (_unused_clause_idx_queue.empty()) {
	new_cl = _clauses.size();
	_clauses.resize(new_cl + 1);
    }
    else {
	new_cl = _unused_clause_idx_queue.front();
	_unused_clause_idx_queue.pop();
    }
    //c. add the clause lits to lits pool
    clause(new_cl).init(lit_pool_end(), n_lits);

    //I want to verify added clauses are either all free or all 0
    bool satisfied = false, is_unit = false, is_conflict = false;
    int num_unknown = 0;
    for (int i=0; i< n_lits; ++i){
	int var_idx = lits[i]>>1;
	if ((unsigned)var_idx >= variables().size()) {
          assert(false);
        }
	int var_sign = lits[i]&0x1;
	lit_pool_push_back( ((var_idx<<1) + var_sign) << 2);
	++variable(var_idx).lits_count(var_sign);
	int lit_value = literal_value(clause(new_cl).literal(i));

	if (lit_value == 1) {
	  satisfied = true;
	}
	else if (lit_value != 0) {
	  ++num_unknown;
	}
    }
    is_conflict = !satisfied && (num_unknown == 0);
    is_unit = !satisfied && (num_unknown == 1);
    assert(_stats.is_solver_started || num_unknown == n_lits);
    lit_pool_push_back(-new_cl); //push in the clause idx in the end
    //d. set the head/tail pointers
    if (clause(new_cl).num_lits() > 1) {
	//add the ht. note: ht must be the last free var
	int max_idx = -1, max_dl = -1;
	CClause & cl = clause(new_cl);
	int i, sz = cl.num_lits();
	int other_ht_idx;
	for (i=0; i< sz; ++i) {
	    int v_idx = cl.literals()[i].var_index();
	    if (variable(v_idx).value()==UNKNOWN) {
		int v_sign = cl.literals()[i].var_sign();
		variable(v_idx).ht_ptr(v_sign).push_back( & cl.literals()[i]);
		cl.literals()[i].set_ht(1);
		other_ht_idx = i;
		break;
	    }
	    else {
		if (variable(v_idx).dlevel() > max_dl) {
		    max_dl = variable(v_idx).dlevel();
		    max_idx = i;
		}
	    }
	}
	if (i >= sz) {
	    //no unknown literals. so use the max dl literal
	    int v_idx = cl.literals()[max_idx].var_index();
	    int v_sign = cl.literals()[max_idx].var_sign();
	    variable(v_idx).ht_ptr(v_sign).push_back( & cl.literals()[max_idx]);
	    cl.literals()[max_idx].set_ht(1);
	    other_ht_idx = max_idx;
	}
	max_idx = -1; max_dl = -1;
	for (i=sz-1; i>=0; --i) {
	    if (i==other_ht_idx ) continue;
	    int v_idx = cl.literals()[i].var_index();
	    if (variable(v_idx).value()==UNKNOWN) {
		int v_sign = cl.literals()[i].var_sign();
		variable(v_idx).ht_ptr(v_sign).push_back( & cl.literals()[i]);
		cl.literals()[i].set_ht(-1);
		break;
	    }
	    else {
		if (variable(v_idx).dlevel() > max_dl) {
		    max_dl = variable(v_idx).dlevel();
		    max_idx = i;
		}
	    }
	}
	if (i < 0) {
	    int v_idx = cl.literals()[max_idx].var_index();
	    int v_sign = cl.literals()[max_idx].var_sign();
	    CLitPoolElement * lit_ptr = & cl.literals()[max_idx];
	    variable(v_idx).ht_ptr(v_sign).push_back(lit_ptr);
	    cl.literals()[max_idx].set_ht(-1);
	}
    }
    //update some statistics
    ++CDatabase::_stats.num_added_clauses; 
    CDatabase::_stats.num_added_literals += n_lits;
    if (is_unit && _stats.is_solver_started) {
      if (n_lits == 1) _addedUnitClauses.push_back(new_cl);
      int lit = find_unit_literal(new_cl);
      assert(lit);
      queue_implication(lit, new_cl);
    }
    else if (addConflicts && is_conflict) {
      _conflicts.push_back(new_cl);
    }
    return new_cl;
}


void CSolver::set_var_value(int v, int value, ClauseIdx ante, int dl)
{
    assert (value == 0 || value == 1);
    CHECK_FULL(dump());
    CHECK(verify_integrity());
    CHECK (cout << "Setting\t" << (value>0?"+":"-") << v 
	   << " at " << dl << " because " << ante<< endl;);
    ++_stats.num_implications ;
    --num_free_variables();
    if (_assignment_hook) {
      (*_assignment_hook)(_assignment_hook_cookie, v, value);
    }
    CVariable & var = _variables[v];
    assert (var.value() == UNKNOWN);
    var.dlevel() = dl;
    var.value() = value;
    var.set_antecedence(ante);
    vector<CLitPoolElement *> & ht_ptrs = var.ht_ptr(value);
    if (dl == dlevel()) 
	set_var_value_with_current_dl(v, ht_ptrs);
    else 
	set_var_value_not_current_dl(v, ht_ptrs);
}


void CSolver::set_var_value_with_current_dl(int v, vector<CLitPoolElement *> & ht_ptrs)
{
    ClauseIdx cl_idx;
    CLitPoolElement * ht_ptr, * other_ht_ptr = NULL, * ptr;
    int dir;
    for (vector <CLitPoolElement *>::iterator itr = ht_ptrs.begin(); itr != ht_ptrs.end(); ++itr) {
	ht_ptr = *itr;
	dir = ht_ptr->direction();
	ptr = ht_ptr;
	while(1) {
	    ptr += dir;
	    if (ptr->val() <= 0) {
		if (dir == 1) 
		    cl_idx = - ptr->val();
		if (dir == ht_ptr->direction()) {
		    ptr = ht_ptr;
		    dir = -dir;
		    continue;
		}
		int the_value = literal_value (*other_ht_ptr);
		if (the_value == 0) //a conflict
		    _conflicts.push_back(cl_idx);
		else if ( the_value != 1) //e.g. unknown
		    queue_implication (other_ht_ptr->s_var(), cl_idx);
		break;
	    }
	    if (ptr->is_ht()) {
		other_ht_ptr = ptr;
		continue;
	    }
	    if (literal_value(*ptr) == 0) 
		continue;
	    //now it's value is either 1 or unknown
	    int v1 = ptr->var_index();
	    int sign = ptr->var_sign();
	    variable(v1).ht_ptr(sign).push_back(ptr);
	    ht_ptr->unset_ht();
	    ptr->set_ht(dir);

	    *itr = ht_ptrs.back();
	    ht_ptrs.pop_back();
	    --itr;
	    break;
	}
    }
}

void CSolver::set_var_value_not_current_dl(int v, vector<CLitPoolElement *> & ht_ptrs)
{
    ClauseIdx cl_idx;
    CLitPoolElement * ht_ptr, * other_ht_ptr = NULL, * ptr, * max_ptr = NULL;
    int dir,max_dl;

    for (vector <CLitPoolElement *>::iterator itr = ht_ptrs.begin(); 
	 itr != ht_ptrs.end(); ++itr) {
	max_dl = -1;
	ht_ptr = *itr;
	dir = ht_ptr->direction();
	ptr = ht_ptr;
	while(1) {
	    ptr += dir;
	    if (ptr->val() <= 0) {
		if (dir == 1) 
		    cl_idx = - ptr->val();
		if (dir == ht_ptr->direction()) {
		    ptr = ht_ptr;
		    dir = -dir;
		    continue;
		}
		if (variable(ht_ptr->var_index()).dlevel() < max_dl) {
		    int v1 = max_ptr->var_index();
		    int sign = max_ptr->var_sign();
		    variable(v1).ht_ptr(sign).push_back(max_ptr);
		    ht_ptr->unset_ht();
		    max_ptr->set_ht(dir);
		    *itr = ht_ptrs.back();
		    ht_ptrs.pop_back();
		    --itr;
		}
		int the_value = literal_value (*other_ht_ptr);
		if (the_value == 0) //a conflict
		    _conflicts.push_back(cl_idx);
		else if ( the_value != 1) //e.g. unknown
		    queue_implication (other_ht_ptr->s_var(), cl_idx);
		break;
	    }
	    if (ptr->is_ht()) {
		other_ht_ptr = ptr;
		continue;
	    }
	    if (literal_value(*ptr) == 0) {
		if (variable(ptr->var_index()).dlevel() > max_dl) {
		    max_dl = variable(ptr->var_index()).dlevel();
		    max_ptr = ptr;
		}
		continue;
	    }
	    //now it's value is either 1 or unknown
	    int v1 = ptr->var_index();
	    int sign = ptr->var_sign();
	    variable(v1).ht_ptr(sign).push_back(ptr);
	    ht_ptr->unset_ht();
	    ptr->set_ht(dir);

	    *itr = ht_ptrs.back();
	    ht_ptrs.pop_back();
	    --itr;
	    break;
	}
    }
}

void CSolver::unset_var_value(int v)
{
    CHECK(cout <<"Unset var " << (variable(v).value()?"+":"-") << v << endl;);
    CVariable & var = variable(v);
    if (var.var_score_pos() < _max_score_pos)
	_max_score_pos = var.var_score_pos();
    var.value() = UNKNOWN;
    var.set_antecedence(NULL_CLAUSE);
    var.dlevel() = -1;
    if (_assignment_hook) {
      (*_assignment_hook)(_assignment_hook_cookie, v, -1);
    }
}

int CSolver::find_max_clause_dlevel(ClauseIdx cl)
{
//if cl has single literal, then dlevel should be 0 
    int max_level = 0;
    if (cl == NULL_CLAUSE || cl == FLIPPED) 
	return dlevel();
    for (int i=0, sz= clause(cl).num_lits(); i<sz;  ++i) {
	int var_idx =((clause(cl).literals())[i]).var_index();
	if (_variables[var_idx].value() != UNKNOWN) {
	    if (max_level < _variables[var_idx].dlevel())
		max_level =  _variables[var_idx].dlevel();
	}
    }
    return max_level; 
}

void CSolver::dump_assignment_stack(ostream & os) {
    cout << "Assignment Stack:  ";
    for (int i=0; i<= dlevel(); ++i) {
	if ((*_assignment_stack[i]).size() > 0)
	if (variable( (*_assignment_stack[i])[0]>>1).get_antecedence()==FLIPPED)
	    cout << "*" ;
	cout << "(" <<i << ":";
	for (unsigned j=0; j<(*_assignment_stack[i]).size(); ++j )
	    cout << ((*_assignment_stack[i])[j]&0x1?"-":"+")
		 << ((*_assignment_stack[i])[j] >> 1) << " ";
	cout << ") " << endl;
    }
    cout << endl;
}


bool CDatabase::is_conflict(ClauseIdx cl)
{
    CLitPoolElement * lits = clause(cl).literals();
    for (int i=0, sz= clause(cl).num_lits(); i<sz;  ++i)
	if (literal_value(lits[i]) != 0)
		return false;
    return true;
}

bool CDatabase::is_satisfied(ClauseIdx cl)
{
    CLitPoolElement * lits = clause(cl).literals();
    for (int i=0, sz= clause(cl).num_lits(); i<sz; ++i) 
	if (literal_value(lits[i]) == 1) 
	    return true;
    return false;
}

int CDatabase::find_unit_literal(ClauseIdx cl) 
{
//if it's not unit, return 0.
    int unassigned = 0;
    for (int i=0, sz= clause(cl).num_lits(); i<sz;  ++i) {
	int var_idx =((clause(cl).literals())[i]).var_index();
	if (_variables[var_idx].value() == UNKNOWN) {
	    if (unassigned == 0) 
		unassigned = clause(cl).literals()[i].s_var();
	    else //more than one unassigned
		return 0;
	}
    }
    return unassigned;
}

void CSolver::delete_unrelevant_clauses(void) 
{
    CHECK_FULL (dump());
    int original_num_deleted = num_deleted_clauses();
    if (CDatabase::_stats.mem_used_up) {
	CDatabase::_stats.mem_used_up = false;
	if (++CDatabase::_stats.mem_used_up_counts < 5) {
	    _params.max_unrelevance = (int) (_params.max_unrelevance * 0.8);
	    if (_params.max_unrelevance < 4)
		_params.max_unrelevance = 4;
	    _params.min_num_clause_lits_for_delete = (int) (_params.min_num_clause_lits_for_delete* 0.8);
	    if (_params.min_num_clause_lits_for_delete < 10)
		_params.min_num_clause_lits_for_delete = 10;
	    _params.max_conflict_clause_length = (int) (_params.max_conflict_clause_length*0.8);
	    if (_params.max_conflict_clause_length < 50 )
		_params.max_conflict_clause_length = 50;
	    CHECK(
	    cout << "Forced to reduce unrelevance in clause deletion. " << endl;
	    cout <<"MaxUnrel: " << _params.max_unrelevance 
		 << "  MinLenDel: " << _params.min_num_clause_lits_for_delete
		 << "  MaxLenCL : " << _params.max_conflict_clause_length << endl;
		);
	}
    }
    //first find out the clause to delete and mark them
    for (vector<CClause>::iterator itr = clauses().begin() + init_num_clauses(); 
	 itr != clauses().end(); ++itr) {
	CClause & cl = * itr;
	if (!cl.in_use() || cl.num_lits() < _params.min_num_clause_lits_for_delete ) continue;
	int val_0_lits = 0, val_1_lits = 0, unknown_lits = 0;
	for (int i=0; i< cl.num_lits(); ++i) {
	    int lit_value = literal_value (cl.literal(i));
  	    if (lit_value == 0 ) ++val_0_lits;
  	    else if (lit_value == 1) ++val_1_lits;
  	    else ++unknown_lits;
	    if (unknown_lits + val_1_lits > _params.max_unrelevance) {
		mark_clause_deleted(cl);
		_unused_clause_idx_queue.push(itr - clauses().begin());
		CHECK (cout << "Deleting Unrelevant clause: " << cl << endl;);
		break;
	    }
	    if (cl.num_lits() > _params.max_conflict_clause_length && 
		(unknown_lits+val_1_lits > 1) ) { //to make sure it's not generating an implication
		                                  //and it's not an antecedence for other var assignment
		mark_clause_deleted(cl);
		CHECK (cout << "Deleting too large clause: " << cl << endl;);
		_unused_clause_idx_queue.push(itr - clauses().begin());
		break;
	    }
	}
    }
    //now delete the index from variables
    if (original_num_deleted == num_deleted_clauses()) 
	return ; //didn't delete anything
    for (vector<CVariable>::iterator itr = variables().begin(); 
	 itr != variables().end(); ++ itr) {
	for (int i=0; i<2; ++i) { //for each phase
	    //delete the h_t index from the vars
	    vector<CLitPoolElement *> & ht_ptr = (*itr).ht_ptr(i);
	    for (vector<CLitPoolElement *>::iterator my_itr = ht_ptr.begin(); 
		 my_itr != ht_ptr.end(); ++my_itr) {
		if ( (*my_itr)->val() <= 0) {
		    *my_itr = ht_ptr.back();
		    ht_ptr.pop_back();
		    --my_itr;
		}
	    }
	}
    }
    CHECK(cout << "Deleting " << num_deleted_clauses() - original_num_deleted << " Clause ";
      cout << " and " << num_deleted_literals() - original_del_lits << " Literals " << endl;);
    CHECK_FULL (dump());
}
//============================================================================================
bool CSolver::time_out(void) 
{
    if ( (current_cpu_time() - _stats.start_cpu_time)/1000.0 > _params.time_limit )
	return true;
    return false;
}

inline bool compare_var_stat(const pair<int, int> & v1, 
			    const pair<int, int> & v2) 
{
    if (v1.second > v2.second) return true;
    return false;
}

void CSolver::update_var_stats(void) 
{
    for(unsigned i=1; i< variables().size(); ++i) {
	CVariable & var = variable(i);
	var.score(0) = var.score(0)/2 + var.lits_count(0) - _last_var_lits_count[0][i];
	var.score(1) = var.score(1)/2 + var.lits_count(1) - _last_var_lits_count[1][i];
	_last_var_lits_count[0][i] = var.lits_count(0);
	_last_var_lits_count[1][i] = var.lits_count(1);
	_var_order[i-1] = pair<int, int>(i, var.score());
    }
    ::stable_sort(_var_order.begin(), _var_order.end(), compare_var_stat);
    for (unsigned i=0; i<_var_order.size(); ++i) 
	variable(_var_order[i].first).var_score_pos() = i;
    _max_score_pos = 0;
}

bool CSolver::decide_next_branch(void)
{
    ++_stats.num_decisions;
    if (!_implication_queue.empty()) {
	//some hook function did a decision, so skip my own decision making.
	//if the front of implication queue is 0, that means it's finished
	//because var index start from 1, so 2 *vid + sign won't be 0. 
	//else it's a valid decision.
	_max_score_pos = 0; //reset the max_score_position.
	return _implication_queue.front().first;
    }
	
    int s_var = 0, s_var2;
    bool done = false;

    unsigned i, var_idx, sign;
    CVariable * ptr;

    for (i=_max_score_pos; i<_var_order.size(); ++i) {
      var_idx = _var_order[i].first;
      ptr = &(variables()[var_idx]);
      if (ptr->value()==UNKNOWN) {
        //move th max score position pointer
        _max_score_pos = i;
        //make some randomness happen
        if (--_params.randomness < _params.base_randomness)
          _params.randomness = _params.base_randomness;

        int randomness = _params.randomness;
        if (randomness >= num_free_variables())
          randomness = num_free_variables() - 1;
        int skip =random()%(1+randomness);
        int index = i;
        while (skip > 0) {
          ++index;
          var_idx = _var_order[index].first;
          ptr = &(variables()[var_idx]);
          if (ptr->value()==UNKNOWN)
            --skip;
        }
        assert (ptr->value() == UNKNOWN);
        sign = ptr->score(0) > ptr->score(1) ? 0 : 1;
        s_var = var_idx + var_idx + sign;
        break;
      }
    }
    if (s_var < 2) done = true;

    if (_decision_hook) {
    decide:
      s_var2 = (*_decision_hook)(_decision_hook_cookie, &done);
      if (done) {
        if (s_var2 == -1) {
          // No more decisions
          return false;
        }
        else {
          // check for more work
          if (!_implication_queue.empty() ||
              _conflicts.size() != 0)
            return false;
          else goto decide;
        }
      }
      else {
        if (s_var2 == -1) {
          // use SAT choice
        }
        else {
          // use decision
          s_var = s_var2;
        }
      }
    }

    if (s_var<2) //no more free vars, solution found,  quit
	return false;
    ++dlevel();
    if (_dlevel_hook) {
      (*_dlevel_hook)(_dlevel_hook_cookie, 1);
    }
    if (dlevel() > _stats.max_dlevel) _stats.max_dlevel = dlevel();
    CHECK (cout << "**Decision at Level " << dlevel() ;
	   cout <<": " << s_var << "\te.g. " << (s_var&0x1?"-":" ") ;
	   cout <<(s_var>>1)  << endl; );
    queue_implication(s_var, NULL_CLAUSE);
    return true;
}

int CSolver::preprocess(bool allowNewClauses) 
{
    //1. detect all the unused variables
  if (!allowNewClauses) {
    vector<int> un_used;
    for (int i=1, sz=variables().size(); i<sz; ++i) {
	CVariable & v = variable(i);
  	if (v.lits_count(0) == 0 && v.lits_count(1) == 0) {
	    un_used.push_back(i);
	    v.value() = 1; 
	    v.dlevel() = -1;
	}
    }
    num_free_variables() -= un_used.size();
    if (_params.verbosity>1 && un_used.size() > 0) {
	cout << un_used.size()<< " Variables are defined but not used " << endl;
	if (_params.verbosity > 2) {
	    for (unsigned i=0; i< un_used.size(); ++i)
		cout << un_used[i] << " ";
	    cout << endl;
	}
    }
    //2. detect all variables with only one phase occuring
    vector<int> uni_phased;
    for (int i=1, sz=variables().size(); i<sz; ++i) {
	CVariable & v = variable(i);
	if (v.value() != UNKNOWN)
	    continue;
  	if (v.lits_count(0) == 0){ //no positive phased lits.
	    queue_implication( i+i+1, NULL_CLAUSE);
	    uni_phased.push_back(-i);
	}
	else if (v.lits_count(1) == 0){ //no negative phased lits.
	    queue_implication( i+i, NULL_CLAUSE);
	    uni_phased.push_back(i);
	}
    }
    if (_params.verbosity>1 && uni_phased.size() > 0) {
	cout << uni_phased.size()<< " Variables only appear in one phase." << endl;
	if (_params.verbosity > 2) {
	    for (unsigned i=0; i< uni_phased.size(); ++i)
		cout << uni_phased[i] << " ";
	    cout <<endl;
	}
    }
  }
    //3. detect all the unit clauses
    for (ClauseIdx i=0, sz=clauses().size(); i<sz; ++i) {
	if (clause(i).num_lits() == 1){ //unit clause
	    queue_implication(find_unit_literal(i), i);
	}
    }

    if(deduce()==CONFLICT) return CONFLICT;
    return NO_CONFLICT;    
}

void CSolver::real_solve(void)
{
    while(1) {
        run_periodic_functions();
	if (decide_next_branch() || !_implication_queue.empty() ||
            _conflicts.size() != 0) {
	    while (deduce()==CONFLICT) { 
		int blevel = analyze_conflicts();
		if (blevel <= 0) {
		    _stats.outcome = UNSATISFIABLE;
		    return;
		}
                else if (_addedUnitClauses.size()) {
                  // reassert added unit clauses
                  unsigned idx = _addedUnitClauses.size()-1;
                  ClauseIdx cl = _addedUnitClauses.back();
                  int lit = find_unit_literal(cl);
                  while (lit != 0) {
                    queue_implication(lit, cl);
                    if (idx == 0) break;
                    cl = _addedUnitClauses[--idx];
                    lit = find_unit_literal(cl);
                  }
                }
	    }
	}
	else {
          _stats.outcome = SATISFIABLE;
          return;
	}
	if (time_out()) { 
	    _stats.outcome = TIME_OUT;
	    return; 
	}
	if (_stats.is_mem_out) {
	    _stats.outcome = MEM_OUT;
	    return; 
	}
    }
}

int CSolver::solve(bool allowNewClauses)
{
    init();
    //preprocess 
    if(preprocess(allowNewClauses)==CONFLICT) {
	_stats.outcome = UNSATISFIABLE;
    }
    else { //the real search
      if (_dlevel_hook) {
        (*_dlevel_hook)(_dlevel_hook_cookie, 1);
      }
      real_solve();
    }
    _stats.finish_cpu_time = current_cpu_time();
    _stats.finish_world_time = current_world_time();
    return _stats.outcome;
}

int CSolver::continueCheck()
{
  real_solve();
  _stats.finish_cpu_time = current_cpu_time();
  _stats.finish_world_time = current_world_time();
  return _stats.outcome;
}

void CSolver::back_track(int blevel)
{
    CHECK (cout << "Back track to " << blevel <<" ,currently in "<< dlevel() << " level" << endl;);
    CHECK_FULL (dump());
    CHECK(verify_integrity());
    assert(blevel <= dlevel());
    for (int i=dlevel(); i>= blevel; --i) {
	vector<int> & assignments = *_assignment_stack[i];
	for (int j=assignments.size()-1 ; j>=0; --j) 
		unset_var_value(assignments[j]>>1);
	num_free_variables() += assignments.size();
	assignments.clear();
	if (_dlevel_hook) {
	  (*_dlevel_hook)(_dlevel_hook_cookie, -1);
	}
    }
    dlevel() = blevel - 1;
    ++_stats.num_backtracks;
    CHECK_FULL (dump());
    CHECK(verify_integrity());
}

int CSolver::deduce(void) 
{
restart:
    while (!_implication_queue.empty() && _conflicts.size()==0) {
	int literal = _implication_queue.front().first;
	int variable_index = literal>>1;
	ClauseIdx cl = _implication_queue.front().second;
	_implication_queue.pop();
	CVariable * the_var = &(variables()[variable_index]);
	if ( the_var->value() == UNKNOWN) { // an implication
	    int dl;
	    if (_params.back_track_complete)
		dl = dlevel();
	    else 
		dl = find_max_clause_dlevel(cl);
	    set_var_value(variable_index, !(literal&0x1), cl, dl);
	    the_var = &(variables()[variable_index]);
	    _assignment_stack[dl]->push_back(literal);
	    CHECK(verify_integrity());
	}
	else if (the_var->value() == (literal&0x1) ) { //a conflict
	    //note: literal & 0x1 == 1 means the literal is in negative phase
	    _conflicts.push_back(cl);
	}
    }
    if (!_conflicts.size() && _deduction_hook) {
      (*_deduction_hook)(_deduction_hook_cookie);
      if (!_implication_queue.empty()) goto restart;
    }
    while(!_implication_queue.empty()) _implication_queue.pop();
    return (_conflicts.size()?CONFLICT:NO_CONFLICT);
}


void CSolver::verify_integrity(void) 
{
}

void CSolver::mark_vars_at_level(ClauseIdx cl, int var_idx, int dl)
{
    for (CLitPoolElement * itr = clause(cl).literals(); (*itr).val() > 0 ; ++ itr) {
	int v = (*itr).var_index();
	if (v == var_idx) 
	    continue;
	else if (variable(v).dlevel() == dl) {
	    if (!variable(v).is_marked()) {
		variable(v).set_marked();
		++ _num_marked;
	    }
	}
	else {
	    assert (variable(v).dlevel() < dl);
	    if (variable(v).in_new_cl() == -1){ //it's not in the new cl
		variable(v).set_in_new_cl((*itr).var_sign());
		_conflict_lits.push_back((*itr).s_var());
	    }
	}
    }
}

int CSolver::analyze_conflicts(void) {
    return conflict_analysis_zchaff();
}

int CSolver::conflict_analysis_zchaff (void) 
{
    assert (_conflicts.size());
    assert (_implication_queue.empty());
    assert (_num_marked == 0);
    int back_level = 0;
    ClauseIdx conflict_cl;
    vector<ClauseIdx> added_conflict_clauses;
    for (int i=0, sz=_conflicts.size(); i<sz; ++i) {
	ClauseIdx cl = _conflicts[i];

	if (!is_conflict(cl)) continue;

	back_level = 0; // reset it
	while (_conflict_lits.size()) {
	    CVariable & var = variable(_conflict_lits.back() >> 1);
	    _conflict_lits.pop_back();
	    assert (var.in_new_cl() != -1);
	    var.set_in_new_cl(-1);
	}
	int max_dlevel = find_max_clause_dlevel(cl); // find the max level, which is the back track level
	bool first_time = true; //its the beginning
	bool prev_is_uip = false;
	mark_vars_at_level (cl, -1 /*var*/, max_dlevel);

	vector <int> & assignments = *_assignment_stack[max_dlevel];
	for (int j = assignments.size() - 1; j >= 0; --j ) { //now add conflict lits, and unassign vars
	    int assigned = assignments[j];
	    if (variable(assigned>>1).is_marked()) {
		variable(assigned>>1).clear_marked();
		-- _num_marked; 
		ClauseIdx ante_cl = variables()[assigned>>1].get_antecedence();

		if ( (_num_marked == 0 && 
		      (!first_time) && 
		      (prev_is_uip == false))
		      || ante_cl==NULL_CLAUSE) { //conclude add clause
		    assert (variable(assigned>>1).in_new_cl()==-1);
		    _conflict_lits.push_back(assigned^0x1);  // add this assignment's reverse, e.g. UIP
		    int conflict_cl = add_clause(_conflict_lits, false);
		    if (conflict_cl < 0 ) {
			_stats.is_mem_out = true;
			_conflicts.clear();
			assert (_implication_queue.empty());
			return 1; 
		    }
		    _conflict_lits.pop_back();  // remove for continue use of _conflict_lits
		    added_conflict_clauses.push_back(conflict_cl);

		    CHECK(cout <<"Conflict clause: " << cl << " : " << clause(cl) << endl;
			  cout << "**Add Clause " <<conflict_cl<< " : "<<clause(conflict_cl) << endl; 
			);

		    prev_is_uip = true;
		    break; //if do this, only one clause will be added.
		}
		else prev_is_uip = false;

		if ( ante_cl != NULL_CLAUSE ) 
		    mark_vars_at_level(ante_cl, assigned>>1/*var*/, max_dlevel);
		else 
		    assert (j == 0);
		first_time = false;
	    }
	}
	back_level = max_dlevel;
	back_track(max_dlevel);	
    }
    assert (_num_marked == 0);
    if (back_level==0) //there are nothing to be done
	    return back_level;

    if (_params.back_track_complete) {
	for (unsigned i=0; i< added_conflict_clauses.size(); ++i) {
	    ClauseIdx cl = added_conflict_clauses[i];
	    if (find_unit_literal(cl)) { //i.e. if it's a unit clause
  		int dl = find_max_clause_dlevel(cl);
  		if (dl < dlevel()) { //thus make sure implied vars are at current dl.
  		    back_track(dl+1);
		}
	    }
	}
    }
    for (int i=0, sz=added_conflict_clauses.size(); i<sz; ++i) {
	conflict_cl = added_conflict_clauses[i];
	int lit = find_unit_literal(conflict_cl);
	if (lit) {
	    queue_implication(lit, conflict_cl);
	}
    }

    _conflicts.clear();

    while (_conflict_lits.size()) {
	CVariable & var = variable(_conflict_lits.back() >> 1);
	_conflict_lits.pop_back();
	assert (var.in_new_cl() != -1);
	var.set_in_new_cl(-1);
    }
    CHECK( dump_assignment_stack(););
    CHECK(cout << "Conflict Analasis: conflict at level: " << back_level;
  	  cout << "  Assertion Clause is " << conflict_cl<< endl; );
    return back_level;
}		
















