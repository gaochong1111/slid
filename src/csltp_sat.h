#ifndef CSLTP_SAT_H
#define CSLTP_SAT_H

#include "noll_form.h"
#include "noll_preds.h"
#include "csltp_order_graph.h"
#include <z3++.h>

class csltp_context {
public:
        csltp_context();

public:
        noll_var_array* lvars; // var environment
        uid_t index_processing; // processing index of atom

        z3::context ctx;
        z3::expr_vector delta_ge1_predicates; // phi^{>=1}_P(\alpha; \beta), corresponding to preds_array
        z3::expr_vector new_bool_vars; // introduce new boolean vars
        z3::expr pure_abs; // abs of Pi and Delta
        z3::expr space_abs; // abs of spatial part
        z3::expr phi_star; // abs of sepaation constraint
};

/**
 *@return 1, if sat
 0, if unsat
 -1,if undef
*/
int csltp_sat_check(noll_form_t *);


/*******************************
 ***  noll logic to abstration *
 ******************************/

/**
 * compute all predicate lfp
 * @param ctx : csltp context
 */
void compute_all_delta_ge1_p(csltp_context& ctx);

/**
 * compute delta_ge1_r
 * @param rule : the rule R
 * @param fargs : the recursive call predicate arguments number
 * @param ctx : csltp context
 * @return expr
 */
z3::expr compute_delta_ge1_r(noll_pred_rule_t* rule, noll_pred_t* pred, z3::expr& phi_pd_abs, csltp_context& ctx);

/**
 * compute the delta_phi_pd
 * @param pred : predicate
 * @param ctx : z3 context
 * @return expr
 */
z3::expr compute_delta_phi_pd(noll_pred_t* pred, z3::context& ctx);



/**
 * abstraction of pure part
 * @param lvars : the local vars
 * @param pure : pure part of formula
 * @param ctx : z3::context
 * @return abs :         z3::expr formula
 */
void abs_pure(noll_pure_t* pure, csltp_context& ctx);

/**
 * abstraction of space part
 * @param lvars : the local vars
 * @param space : space part of formula
 * @param ctx : z3::context
 * @param res :         z3::expr forumla
 */
void abs_space(noll_space_t* space, csltp_context& ctx);

/**
 * compute phi_star
 * @param ctx : csltp_context
 */
void abs_phi_star(csltp_context& ctx);



/**
 * compute lfp(pred)
 * @param pred: the predicate definition
 * @return ogset: the least fixed point: order graph set
 */
OrderGraphSet lfp(noll_pred_t* pred);


/**
 * create expr by name
 * @param str : name or constant
 * @param ctx : z3 context
 * @return expr
 */
z3::expr create_expr_by_name(string str, z3::context& ctx);


/**
 * create expr by vid for args
 * @param lvars : var environment
 * @param vid : the varid or constant
 * @param ctx : z3 context
 * @return expr
 */
z3::expr create_expr_args(noll_var_array* lvars, uid_t vid, z3::context& ctx);


/**
 * order graph to z3 expr
 * @param og : order graph
 * @param ctx : z3 context
 * @return expr : expr
 */
z3::expr graph2expr(OrderGraph& og, z3::context& ctx);


/**
 * var to z3 expr
 * @param var : var
 * @param ctx : z3context
 * @return expr : expr
 */
z3::expr var2expr(noll_var_t* var, csltp_context& ctx);


/**
 * introduce a new boolean var
 * @param var : var
 * @param ctx : context
 * @return res : bool var of z3
 */
z3::expr introduce_bool_var(noll_var_t* var, csltp_context& ctx);

/**
 * data term to expr
 * @param lvars : var array
 * @param dt : data term
 * @param ctx : z3 context
 * @return expr: expr
 */
z3::expr dterm2expr(noll_dterm_t* dt, csltp_context& ctx);

/**
 * dform to expr
 * @param df : data formula
 * @param ctx : csltp_context
 * @return expr
 */
z3::expr dform2expr(noll_dform_t* df, csltp_context& ctx);


/*******************************
 ***  noll logic to graph   ***
******************************/

/**
 * @param rule : predicate rule definition
 * @param og: output order graph related data graph (Rat)
 */
void pure2graph(noll_pred_rule_t* rule, OrderGraph& og);

/**
 * extract alpha and beta from predicate definition
 * @param pred : predicate definition
 * @param alpha : output alpha
 * @param beta : output beta
 */
void extractAlphaBeta(noll_pred_t* pred, vector<Vertex>& alpha, vector<Vertex>& beta);

/**
 * extract delta, gamma, epsilon
 * @param rule: recursive rule
 * @param fargs: the predicate argument number
 * @param delta_gamma, epsilon : output
 */
void extractRecCallDataPara(noll_pred_rule_t* rule, uid_t fargs, vector<Vertex>& delta, vector<Vertex>& gamma_epsilon, set<Vertex>& constant_set);

/**
 * vector (no same elements) to set
 * @param vec : vector
 * @param v_set : output
 */
void vec2set(vector<Vertex>& vec, set<Vertex>& v_set);

/**
 * extract constant from the inductive rule
 * @param rule : the inductive rule
 * @param constant_set : constant vertex set
 */
void extract_constant_from_rule_pure(noll_pred_rule_t* rule, set<Vertex>& constant_set);

/**
 * create constant graph
 * @param constant_set : the set of constant
 * @param og_cons : the output graph
 */
void create_constant_order_graph(set<Vertex>& constant_set, OrderGraph& og_cons);


/*******************************
 ***  print functions        ***
 ******************************/

void print_vertex(vector<Vertex> vec, string msg);

/**
 * print the order graph lfp for $prefix_G_$i.dot
 * @param ogset : order graph set
 * @param prefix : the file prefix
 */
void print_order_graph_set(OrderGraphSet& ogs, string msg);






#ifdef __cplusplus
extern "C" {
#endif
// declare some c-like functions which may be useed by cpp file

#ifdef __cplusplus
}
#endif


#endif // csltp_sat.h
