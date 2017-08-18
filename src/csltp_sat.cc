#include "csltp_sat.h"
#include<sstream>
#include<iostream>

/**
 *@return 1, if sat
 0, if unsat
 -1,if undef
*/
int csltp_sat_check(noll_form_t *) {
        //TODO: check the formula sat
        return -1;
}

/**
 * @param rule : predicate rule definition
 * @param og: output order graph related data graph (Rat)
 */
void pure2graph(noll_pred_rule_t* rule, OrderGraph& og) {
        noll_var_array * vars = rule->vars;
        // add vertex
        uid_t length_vars = noll_vector_size (vars);
        for (uid_t i = 0; i < length_vars; i++)
        {
                noll_var_t *vi = noll_vector_at (vars, i);
                noll_type_t *ti = vi->vty;
                if (ti->kind == NOLL_TYP_RAT) {
                        // add vertex
                        string name(vi->vname);
                        Vertex vertex(name);
                        og.addVertex(vertex);
                }
        }

        //add edge
        noll_pure_t* phi = rule->pure;

        for (uid_t l = 0; l < phi->size; l++)
        {
                for (uid_t c = l+1; c < phi->size; c++)
                {
                        noll_var_t* var1 = noll_vector_at (vars, l);
                        noll_var_t* var2 = noll_vector_at(vars, c);

                        if (var1->vty->kind == NOLL_TYP_RAT
                            && var2->vty->kind == NOLL_TYP_RAT
                            && noll_pure_matrix_at (phi, l, c) == NOLL_PURE_EQ) {
                                Vertex v1(var1->vname);
                                Vertex v2(var2->vname);
                                Edge e1(v1, LABEL_LE, v2);
                                Edge e2(v2, LABEL_LE, v1);
                                og.addEdge(e1);
                                og.addEdge(e2);
                        }
                }
        }

        // data formula

        noll_dform_array* dfs = phi->data;

        if (dfs == NULL) return;

        for (uint_t i = 0; i < noll_vector_size (dfs); i++)
        {
                noll_dform_t* df = noll_vector_at(dfs, i);

                noll_var_t* v1 = NULL;
                noll_var_t* v2 = NULL;

                if (df->p.targs != NULL && noll_vector_size (df->p.targs) == 2) {
                        noll_dterm_t* term1 = noll_vector_at (df->p.targs, 0);
                        noll_dterm_t* term2 = noll_vector_at (df->p.targs, 1);

                        if (term1->kind == NOLL_DATA_VAR) {
                                v1 =  noll_vector_at (vars, term1->p.sid);
                                if (v1->vty->kind == NOLL_TYP_RAT) {
                                        if (term2->kind == NOLL_DATA_VAR) {
                                                v2 =  noll_vector_at (vars, term2->p.sid);
                                                if (v2->vty->kind != NOLL_TYP_RAT) {
                                                        v2 = NULL;
                                                }
                                        }

                                        if (term2->kind == NOLL_DATA_RAT) {
                                                // TODO RAT constant
                                        }
                                }
                        }
                }

                if (v1 != NULL && v2 != NULL) {
                        Vertex vertex1(v1->vname);
                        Vertex vertex2(v2->vname);

                        if (df->kind == NOLL_DATA_EQ) {
                                Edge eq_e1(vertex1, LABEL_LE, vertex2);
                                Edge eq_e2(vertex2, LABEL_LE, vertex1);
                                og.addEdge(eq_e1);
                                og.addEdge(eq_e2);
                        } else if (df->kind == NOLL_DATA_LT) {
                                Edge lt_e(vertex1, LABEL_LT, vertex2);
                                og.addEdge(lt_e);
                        } else if (df->kind == NOLL_DATA_GT) {
                                Edge gt_e(vertex2, LABEL_LT, vertex1);
                                og.addEdge(gt_e);
                        } else if (df->kind == NOLL_DATA_LE) {
                                Edge le_e(vertex1, LABEL_LE, vertex2);
                                og.addEdge(le_e);
                        } else if (df->kind == NOLL_DATA_GE) {
                                Edge ge_e(vertex2, LABEL_LE, vertex1);
                                og.addEdge(ge_e);
                        }
                }
        }
}

/**
 * extract alpha and beta from predicate definition
 * @param pred : predicate definition
 * @param alpha : output alpha
 * @param beta : output beta
 */
void extractAlphaBeta(noll_pred_t* pred, vector<Vertex>& alpha, vector<Vertex>& beta) {
        uid_t fargs = pred->def->fargs;
        noll_var_array* vars = pred->def->vars;
        noll_var_t *vi = NULL;
        for (uid_t i=2; i<= fargs/2; i++) {
                vi = noll_vector_at (vars, i);
                if (vi->vty->kind == NOLL_TYP_RAT) {
                        Vertex v(vi->vname);
                        alpha.push_back(v);
                }
        }
        for (uid_t i=fargs/2+2; i<=fargs; i++) {
                vi = noll_vector_at (vars, i);
                if (vi->vty->kind == NOLL_TYP_RAT) {
                        Vertex v(vi->vname);
                        beta.push_back(v);
                }
        }
}

/**
 * extract delta, gamma, epsilon
 * @param rule: recursive rule
 * @param fargs: the predicate argument number
 * @param delta, gamma, epsilon : output
 */
void extractRecCallDataPara(noll_pred_rule_t* rule, uid_t fargs, vector<Vertex>& delta, vector<Vertex>& gamma, vector<Vertex>& epsilon) {
        // TODO;....fix bug
        noll_var_array* lvars = rule->vars;

        noll_space_array* sep = rule->rec->m.sep;
        noll_space_t* phi = noll_vector_at(sep, 0);

        noll_space_t* phi_delta = NULL;

        // cout <<"args:" <<noll_vector_at (phi->m.ls.args, fargs/2)<<endl;
        if (noll_vector_at (phi->m.ls.args, fargs/2) == 0) { // nil
                phi_delta =  noll_vector_at(sep, 1);
        } else {
                phi_delta = phi;
                phi = noll_vector_at(sep, 1);
        }

        // delta
        for (uid_t i = 1; i < fargs/2; i++)
        {
                uint_t vid = noll_vector_at (phi_delta->m.ls.args, i);

                noll_var_t *vi = noll_vector_at (lvars, vid);
                if (vi->vty->kind == NOLL_TYP_RAT) {
                        Vertex v(vi->vname);
                        delta.push_back(v);
                } else {
                        // TODO. deal with constant
                }
        }


        // gamma
        for (uid_t i = 1; i < fargs/2; i++)
        {
                uint_t vid = noll_vector_at (phi->m.ls.args, i);

                noll_var_t *vi = noll_vector_at (lvars, vid);
                if (vi->vty->kind == NOLL_TYP_RAT) {
                        Vertex v(vi->vname);
                        gamma.push_back(v);
                } else {
                        // TODO. deal with constant
                }
        }

        // epsilon
        for (uid_t i = fargs/2+1; i < fargs; i++)
        {
                uint_t vid = noll_vector_at (phi->m.ls.args, i);

                noll_var_t *vi = noll_vector_at (lvars, vid);
                if (vi->vty->kind == NOLL_TYP_RAT) {
                        Vertex v(vi->vname);
                        epsilon.push_back(v);
                } else {
                        // TODO. deal with constant
                }
        }
}

void print_vertex(vector<Vertex> vec, string msg) {
        cout<<msg<<endl;
        for (uid_t i=0; i<vec.size(); i++) {
                cout<<vec[i]<<endl;
        }
        cout<<endl;
}

void vec2set(vector<Vertex>& vec, set<Vertex>& v_set) {
        for (uid_t i=0; i<vec.size(); i++) {
                v_set.insert(vec[i]);
        }
}

/**
 * compute lfp(pred)
 * @param pred: the predicate definition
 * @return ogset: the least fixed point: order graph set
 */
OrderGraphSet lfp(noll_pred_t* pred) {
        // init: construct G0 by base rule
        noll_pred_rule_t* base_rule = noll_vector_at (pred->def->base_rules, 0);
        uid_t fargs = pred->def->fargs;
        vector<Vertex> alpha;
        vector<Vertex> beta;

        extractAlphaBeta(pred, alpha, beta);

        // print_vertex(alpha, "alpha:");
        // print_vertex(beta, "beta:");

        OrderGraph g0;

        pure2graph(base_rule, g0);

        // g0.printAsDot("g0.dot");

        // standard iteratiron:
        OrderGraphSet ogset_new;
        OrderGraphSet ogset;
        ogset.addOrderGraph(g0);

        while(!(ogset==ogset_new)) {
                ogset_new = ogset;

                // for all recursive rules
                noll_pred_rule_array* rec_rules = pred->def->rec_rules;

                uid_t length_rules = noll_vector_size(rec_rules);

                for (uid_t k=0; k<length_rules; k++) {
                        noll_pred_rule_t* rule = noll_vector_at(rec_rules, k);
                        vector<Vertex> delta;
                        vector<Vertex> gamma;
                        vector<Vertex> epsilon;

                        extractRecCallDataPara(rule, fargs, delta, gamma, epsilon);
                        // print_vertex(delta, "delta:");
                        // print_vertex(gamma, "gamma:");
                        // print_vertex(epsilon, "epsilon:");

                        // T_R(G)
                        for (int i=0; i<ogset.size(); i++) {
                                for (int j=0; j<ogset.size(); j++) {
                                        OrderGraph og1 = ogset.at(i);
                                        OrderGraph og2 = ogset.at(j);

                                        // g_delta constructed by recursive rule (data constraint)
                                        OrderGraph g_delta;
                                        pure2graph(rule, g_delta);

                                        // substitution1
                                        og1.substitution(alpha, delta);

                                        vector<Vertex> old_vs2 = alpha;
                                        old_vs2.insert(old_vs2.end(), beta.begin(), beta.end());
                                        vector<Vertex> new_vs2 = gamma;
                                        new_vs2.insert(new_vs2.end(), epsilon.begin(), epsilon.end());

                                        // print_vertex(old_vs2, "old_vs2:");
                                        // print_vertex(new_vs2, "new_vs2:");
                                        // substitution2
                                        og2.substitution(old_vs2, new_vs2);

                                        //union
                                        g_delta.unionGraph(og1);
                                        g_delta.unionGraph(og2);

                                        //saturate
                                        g_delta.saturate();

                                        if (g_delta.isConsistent()) {
                                                // restriction
                                                set<Vertex> v_set;
                                                vec2set(old_vs2, v_set);
                                                g_delta.restriction(v_set);

                                                ogset.addOrderGraph(g_delta);
                                        }
                                }
                        }
                }
        }

        /*
        cout <<"the result size:" <<ogset.size()<<endl;

        for (int i=0; i<ogset.size(); i++) {
                stringstream ss;
                ss << "G"<<i<<".dot";
                ogset.at(i).printAsDot(ss.str());
        }
        */
        return ogset;
}
