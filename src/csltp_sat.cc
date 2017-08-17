#include "csltp_sat.h"

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
 * compute lfp(pred)
 * @param pred: the predicate definition
 * @return ogset: the least fixed point: order graph set
 */
OrderGraphSet lfp(noll_pred_t* pred) {
        // TODO: compute lfp

        // init: construct G0 by base rule
        noll_pred_rule_t* base_rule = noll_vector_at (pred->def->base_rules, 0);
        noll_var_array * vars = base_rule->vars;
        OrderGraph g0;
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
                        g0.addVertex(vertex);
                }
        }

        //add edge
        noll_pure_t* phi = base_rule->pure;

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
                                g0.addEdge(e1);
                                g0.addEdge(e2);
                        }
                }
        }
        g0.printAsDot("g0.dot");



        // standard iteratiron:
        OrderGraphSet ogset_new;
        OrderGraphSet ogset;
        ogset.addOrderGraph(g0);

        while(!(ogset==ogset_new)) {
                ogset_new = ogset;

                for (int i=0; i<ogset.size(); i++) {
                        for (int j=0; j<ogset.size(); j++) {
                                OrderGraph og1 = ogset.at(i);
                                OrderGraph og2 = ogset.at(j);


                                // g_delta constructed by recursive rule
                                OrderGraph g_delta;

                                //substitution1

                                //substitution2


                        }
                }



        }

        return ogset;
}
