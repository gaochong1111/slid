#include "noll_form.h"
#include "noll.h"
#include <stdio.h>

/**
 * @brief  The symbol used in the tree encoding and in tree automata
 */
typedef struct noll_ta_symbol
{
  /// The type of the label (see enum @p noll_tree_label_type_t)
  unsigned char label_type;

  union
  {
    /// The structure used for allocated nodes (for label_type ==
    /// NOLL_TREE_LABEL_ALLOCATED)
    struct
    {
      /// The selectors
      noll_uid_array *sels;

      /// Variables that might alias with the node
      noll_uid_array *vars;

      /// The (least) marking of the node
      noll_uid_array *marking;
    } allocated;

    /// Marking of the aliased node (for label_type ==
    /// NOLL_TREE_LABEL_ALIASING_MARKING)
    struct
    {
      /// The marking
      noll_uid_array *marking;

      /// Identifier of the relation (of the type noll_alias_marking_rel_t)
      unsigned char id_relation;
    } alias_marking;

    /// Name of the variable the node is aliased to (for label_type ==
    /// NOLL_TREE_LABEL_ALIASING_VARIABLE)
    uid_t alias_var;

    /// Higher-order predicate (for label_type == NOLL_TREE_LABEL_HIGHER_PRED)
    struct
    {
      /// the higher-order predicate represented by the symbol
      const noll_pred_t *pred;

      /// Variables that might alias with the node
      noll_uid_array *vars;

      /// The (least) marking of the node
      noll_uid_array *marking;
    } higher_pred;
  };

  /// The string representation (for humans)
  char *str;
} noll_ta_symbol_t;
int tabn=0;



void printLowerBoolMatrix(_Bool **m, int size) ;
void printDtermArray(noll_dterm_array* dterms);
void printDterm(noll_dterm_t* dterm);
void printDformArray(noll_dform_array* dforms);
void printDform(noll_dform_t* dform);
char* getEnumTyp(int value);
char* getEnumDataOp(int value);
char* getEnumTreeLabelType(int value);
void printNormalArray( noll_uid_array* arr);
void printTaSymbolArray(noll_ta_symbol_array* arr );
void printTaSymbol(const noll_ta_symbol_t* arr);
void printPredArray(noll_pred_array* arr);
void printPred(noll_pred_t* pred) ;
void printPredBinding(noll_pred_binding_t* def);
void printPredTyping(noll_pred_typing_t* typ);
char*  getEnumPredKind(int value);
void printVarArray(noll_var_array* arr);
void printVar(noll_var_t* var);
void printPredRuleArray(noll_pred_rule_array* arr);
void printPredRule(noll_pred_rule_t* predrule);
char* getEnumScope(int value);
void printPure(noll_pure_t* pure);
void printUpperMatrix(noll_pure_op_t ** m, uint_t size) ;
char* getEnumPuerOp(int value);
void printSpace(noll_space_t* space) ;
void printSpaceArray(noll_space_array* arr) ;
void printPto(noll_pto_t* pto);
void printLs(noll_ls_t* ls);
char* getEnumSpaceOp(int value);
void printExp(noll_exp_t* exp);
char* getEnumExpKind(int value) ;
void printTAB();
void printEntl(noll_entl_t* entl);
char* getEnumLogic(int value);
char* getEnumFormKind(int value);
void printSat(noll_sat_t* sat) ;
void printSatArray(noll_sat_array* arr) ;
void printHom(noll_hom_t* hom);
void printMatrix(noll_uid_array** m, int size) ;
void printRMatrix(noll_uid_array** m, int size) ;
void printShomArray(noll_shom_array* arr) ;

void printShom(noll_shom_t* shom);
void printFormInfo(noll_form_info_t* forminfo);
void printForm(noll_form_t* form);
void printFormArray(noll_form_array* arr) ;
void printShareArray(noll_share_array* arr) ;
void printShare(noll_atom_share_t* share) ;
char* getEnumShareOp(int value);
void printEdgeArray(noll_edge_array* arr) ;

void printSatSpaceArray(noll_sat_space_array* arr) ;
void printSatSpace(noll_sat_space_t* satspace) ;
void printLowerMatrix(uid_t **var_pure, int size) ;
void printStermArray(noll_sterm_array* arr) ;
void printSterm(noll_sterm_t* sterm) ;
char* getEnumStermKind(int value) ;

void printGraphArray(noll_graph_array* arr) ;

void printGraph(noll_graph_t* graph);

void printEdge(noll_edge_t* edge);
void printSatIn(noll_sat_in_t* satin) ;
void printSatInArray(noll_sat_in_array* arr) ;
void printRecordArray(noll_record_array* arr) ;
void printRecord(noll_record_t* record);
void printFieldArray(noll_field_array* arr) ;
void printField(noll_field_t* field) ;
char* getEnumFieldKind(int value) ;

/*typedef enum
  {
    NOLL_PFLD_NONE = 0,
    NOLL_PFLD_BCKBONE,           F^0
    NOLL_PFLD_INNER,            F^1
    NOLL_PFLD_NULL,              F^2 needed?
    NOLL_PFLD_BORDER,            F^2
    NOLL_PFLD_NESTED,
    NOLL_PFLD_DATA
  } noll_field_e;*/


  char* getEnumFieldKind(int value) {
  	switch(value) {
  		case 0:
  				return "NOLL_PFLD_NONE";
  		case 1:
  			return "NOLL_PFLD_BCKBONE";
  		case 2:
  			return "NOLL_PFLD_INNER";
  		case 3:
  			return "NOLL_PFLD_NULL";
  		case 4:
  			return "NOLL_PFLD_BORDER";
  		case 5:
  			return "NOLL_PFLD_NESTED";
  		default:
  			return "NOLL_PFLD_DATA";
  	}
  }
  noll_typ_t t;
/*  typedef struct noll_field_t
  {
    char *name;                 // declaration name
    uid_t fid;                  // field identifier
    uid_t src_r;                // identifier of the source record
    uid_t pto_r;                // identifier of the target record / or UNDEFINED_ID for data
    noll_typ_t pto_ty;          // kind of type for pto
    uid_t order;                // order number wrt use in predicates
    uid_t pid;                  // predicate where the fields is used in the matrix
    noll_field_e kind;          // kind of the field wrt predicate pid
  } noll_field_t;*/
void printField(noll_field_t* field)  {
	printTAB();printf("Field:\n");
	if (field) {
		printTAB();printf("{\n");tabn++;
			printTAB();printf("name=%s\n",field->name);
			printTAB();printf("fid=%d\n",field->fid);
			printTAB();printf("src_r=%d\n",field->src_r);
			printTAB();printf("pto_r=%d\n",field->pto_r);
			printTAB();printf("order=%d\n",field->order);
			printTAB();printf("pid=%d\n",field->pid);
			printTAB();printf("pto_ty=%s\n",getEnumTyp(field->pto_ty));
			printTAB();printf("kind=%s\n",getEnumFieldKind(field->kind));
		tabn--;	printTAB();printf("}\n");
	}
}

/*typedef struct noll_record_t
  {
    char *name;                 // declaration name
    uid_t rid;                  // record identifier, 0 for void*
    noll_uid_array *flds;       // fields of this record
  } noll_record_t;*/
void printRecord(noll_record_t* record) {
	printTAB();printf("Record:\n");
	if (record) {
		printTAB();printf("{\n");tabn++;
			printTAB();printf("name=%s\n",record->name);
			printTAB();printf("rid=%d\n",record->rid);
			printTAB();printf("rid=\n");
					printNormalArray(record->flds);
		tabn--;	printTAB();printf("}\n");
	}
}

void printFieldArray(noll_field_array* arr) {
	printTAB();printf("FieldArray: \n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printField(arr->data_[i]);
				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}

void printRecordArray(noll_record_array* arr) {
	printTAB();printf("RecordArray: \n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printRecord(arr->data_[i]);
				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}

char* getEnumEdgeKind(int value) ;

void printTAB() {
	int i=0;
	while(i++<tabn) {
		printf("\t");
	}
}

/*typedef enum
{
  NOLL_EDGE_DIFF = 0, NOLL_EDGE_PTO, NOLL_EDGE_PRED, NOLL_EDGE_OTHER
} noll_edge_e;*/
char* getEnumEdgeKind(int value)  {
	switch(value) {
		case 0:
				return "NOLL_EDGE_DIFF";
		case 1:
			return "NOLL_EDGE_PTO";
		case 2:
			return "NOLL_EDGE_PRED";
		default:
			return "NOLL_EDGE_OTHER";
	}
}
/*typedef struct noll_edge_s
{
  noll_edge_e kind;             // kind of edge
  noll_uid_array *args;         // array of nodes args[0] = src node, args[1] = dst node
  uint_t label;                 // index of the field or of the predicate
  uint_t bound_svar;            // index of the set variable in slocs_array bounded to the edge, or UNDEFINED_ID
  uint_t id;                    // TODO: id of this edge
  noll_uid_array *impl;         // array of edges implying this one or NULL (related to overlapping)
  noll_uid_array *ssep;         // array of edges strongly separated from this one or NULL
} noll_edge_t;*/
void printEdge(noll_edge_t* edge) {
	printTAB();printf("Edge:\n");
	if (edge) {
		printTAB();printf("{\n");tabn++;
			printTAB();printf("kind=%s\n",getEnumEdgeKind(edge->kind));
			printTAB();printf("args=\n");
					printNormalArray(edge->args);

			printTAB();printf("label=%d\n",edge->label);
			printTAB();printf("bound_svar=%d\n",edge->bound_svar);
			printTAB();printf("id=%d\n",edge->id);
			printTAB();printf("impl=\n");
					printNormalArray(edge->impl);
			printTAB();printf("ssep=\n");
					printNormalArray(edge->ssep);
		tabn--;	printTAB();printf("}\n");
	}
}



void printEdgeArray(noll_edge_array* arr) {
	printTAB();printf("EdgeArray: \n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printEdge(arr->data_[i]);
				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}



void printMatrix(noll_uid_array** m, int size) {
	printTAB();printf("Matrix:\n");
		if (m) {
			printTAB();printf("[\n");tabn++;
			 for (uint_t vi = 0; vi < size; vi++)
			    {
			      if (m[vi] != NULL)
			        {
			          printTAB();printf ( "\tn%d --> ", vi);
			          for (uint_t i = 0; i < m[vi]->size_; i++)
			        	  printf ("e%d, ",m[vi]->data_[i]);
			        }
			      printf("\n");
			    }
			 tabn--;printTAB();printf("]\n");
		}
}

void printRMatrix(noll_uid_array** m, int size) {
	printTAB();printf("RMatrix:\n");
		if (m) {
			printTAB();printf("[\n");tabn++;
			 for (uint_t vi = 0; vi < size; vi++)
			    {
			      if (m[vi] != NULL)
			        {
			          printTAB();printf ( "\tn%d <-- ", vi);
			          for (uint_t i = 0; i < m[vi]->size_; i++)
			        	  printf ("e%d, ",m[vi]->data_[i]);
			        }
			      printf("\n");
			    }
			 tabn--;printTAB();printf("]\n");

		}
}

/*typedef struct noll_graph_t
{
  uint_t nodes_size;            // the number of nodes in the graph
  noll_var_array *lvars;        // graph environment
  noll_var_array *svars;
  uint_t *var2node;             // variables to node labels, array of size of lvars
  noll_edge_array *edges;       // the set of edges in the graph, excluding difference
  noll_uid_array **mat;         // adjacency matrix, mat[i] is the list of edge identifiers from node i
  noll_uid_array **rmat;        // reverse adjacency matrix, rmat[i] is the list of edge identifiers to node i
  bool **diff;                  // low-diagonal matrix, diff[n1][n2] = true iff n1 != n2 and n1 > n2
  noll_dform_array *data;       // data constraints over lvars
  bool isDataComplete;          // all diff and quality constraints are pushed in data ?
  uint_t *sloc2edge;            // mapping set variables to edges in graph
  noll_share_array *share;      // TODO: sharing constraints (on set variables) (related to overlapping)
  bool isComplete;              // if all implicit constraints have been computed
  bool is_precise;              // if graph is precise
} noll_graph_t;*/

void printGraph(noll_graph_t* graph) {
	printTAB();printf("Graph:\n");
	if (graph) {
		printTAB();printf("{\n");tabn++;
			printTAB();printf("nodes_size=%d\n",graph->nodes_size);
			printTAB();printf("lvars=\n");
				printVarArray(graph->lvars);
			printTAB();printf("svars=\n");
				printVarArray(graph->svars);
			printTAB();printf("var2node=\n");
					printTAB();printf("[\n");tabn++;
							int i=0;
							printTAB();
							while(i++<graph->lvars->size_) {
									printf("%d\t", graph->var2node[i]);
							}
					tabn--;printTAB();printf("]\n");
			printTAB();printf("edges=\n");
					printEdgeArray(graph->edges);
			printTAB();printf("mat=\n");
					printMatrix(graph->mat,graph->nodes_size);
			printTAB();printf("rmat=\n");
					printRMatrix(graph->rmat,graph->nodes_size);
			printTAB();printf("diff=\n");
					printLowerBoolMatrix(graph->diff,graph->nodes_size);
			printTAB();printf("data=\n");
					printDformArray(graph->data);
			printTAB();printf("isDataComplete=%d\n",graph->isDataComplete);
			printTAB();printf("sloc2edge=\n");
					printTAB();printf("[\n");tabn++;
							i=0;
							printTAB();
							while(i++<graph->lvars->size_) {
									printf("%d\t", graph->var2node[i]);
							}
					tabn--;printTAB();printf("]\n");
					printTAB();printf("share=\n");
							printShareArray(graph->share);
					printTAB();printf("isComplete=%d\n",graph->isComplete);
					printTAB();printf("is_precise=%d\n",graph->is_precise);
		tabn--;	printTAB();printf("}\n");
	}
}

void printGraphArray(noll_graph_array* arr) {
	printTAB();printf("GraphArray: \n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printGraph(arr->data_[i]);
				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}


/*  typedef enum noll_sterm_kind_t
  {
    NOLL_STERM_LVAR = 0, NOLL_STERM_SVAR, NOLL_STERM_PRJ, NOLL_STERM_OTHER
  } noll_sterm_kind_t;*/
char* getEnumStermKind(int value) {
	switch(value) {
		case 0:
				return "NOLL_STERM_LVAR";
		case 1:
			return "NOLL_STERM_SVAR";
		case 2:
			return "NOLL_STERM_PRJ";
		default:
			return "NOLL_STERM_OTHER";
	}
}


/*typedef struct noll_sterm_t
  {
    noll_sterm_kind_t kind;
    uid_t lvar;                 // location variable, UNDEFINED_ID if kind == NOLL_STERM_SVAR
    uid_t svar;                 // set of locations variable, UNDEFINED_ID if kind == NOLL_STERM_LVAR
  } noll_sterm_t;*/
void printSterm(noll_sterm_t* sterm)  {
	printTAB();printf("Sterm:\n");
	if (sterm) {
		printTAB();printf("{\n");tabn++;
			printTAB();printf("kind=%s\n",getEnumShareOp(sterm->kind));
			printTAB();printf("lvar=%d\n",sterm->lvar);
			printTAB();printf("svar=%d\n",sterm->svar);
		tabn--;	printTAB();printf("}\n");
	}
}


void printStermArray(noll_sterm_array* arr) {
	printTAB();printf("StermArray: \n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printSterm(arr->data_[i]);
				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}



/*  typedef enum noll_share_op_t
  {
    NOLL_SHARE_IN = 0,          \in
    NOLL_SHARE_NI,               \not\in
    NOLL_SHARE_SUBSET,          \subseteq
    NOLL_SHARE_OTHER
  } noll_share_op_t;*/
char* getEnumShareOp(int value) {
	switch(value) {
		case 0:
				return "NOLL_SHARE_IN";
		case 1:
			return "NOLL_SHARE_NI";
		case 2:
			return "NOLL_SHARE_SUBSET";
		default:
			return "NOLL_SHARE_OTHER";
	}
}



/*  typedef struct noll_atom_share_t
  {
    noll_share_op_t kind;       // kind of constraint
    noll_sterm_t *t_left;       // term left
    noll_sterm_array *t_right;  // term right = union of terms
  } noll_atom_share_t;*/
void printShare(noll_atom_share_t* share) {
	printTAB();printf("Share:\n");
	if (share) {
		printTAB();printf("{\n");tabn++;
			printTAB();printf("kind=%s\n",getEnumShareOp(share->kind));
			printTAB();printf("t_left=\n");
				printSterm(share->t_left);
			printTAB();printf("t_right=\n");
				printStermArray(share->t_right);
		tabn--;	printTAB();printf("}\n");
	}
}

void printShareArray(noll_share_array* arr) {
	printTAB();printf("ShareArray: \n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printShare(arr->data_[i]);
				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}

/* typedef struct noll_form_t
  {
    noll_form_kind_t kind;      // kind of formula
    noll_var_array *lvars;      // local variables
    noll_var_array *svars;
    noll_pure_t *pure;          // pure part
    noll_space_t *space;        // space part
    noll_share_array *share;    // sharing part
  } noll_form_t;*/
void printForm(noll_form_t* form) {
	printTAB();printf("Form:\n");
	if (form) {
		printTAB();printf("{\n");tabn++;
			printTAB();printf("kind=%s\n",getEnumFormKind(form->kind));
			printTAB();printf("lvars=\n");
				printVarArray(form->lvars);
			printTAB();printf("svars=\n");
				printVarArray(form->svars);
			printTAB();printf("pure=\n");
				printPure(form->pure);
			printTAB();printf("space=\n");
				printSpace(form->space);
			printTAB();printf("share=\n");
				printShareArray(form->share);
		tabn--;	printTAB();printf("}\n");
	}
}


void printFormArray(noll_form_array* arr) {
	printTAB();printf("FormArray: \n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printForm(arr->data_[i]);
				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}


/*
typedef struct noll_form_info_s
{
  bool *used_lvar;              // bitset of size of locs_array //
  bool *used_svar;              // bitset of size of slocs_array //
  bool *used_pred;              // bitset of size of pred_array //
  bool *used_flds;              // bitset of size of fields_array //

  uint_t lvar_size;             // number of used lvar //
  uint_t svar_size;             // number of used svar //
  uint_t fld_size;              // number of used fields //
  uint_t pto_size;              // number of pto atoms //
  uint_t ls_size;               // number of pred atoms //

} noll_form_info_t;*/
void printFormInfo(noll_form_info_t* forminfo) {
	printTAB();printf("FormInfo:\n");
	if (forminfo) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("lvar_size=%d\n",forminfo->lvar_size);
		printTAB();printf("used_lvar=\n");
		printTAB();printf("[\n");tabn++;
				int i=0;
				printTAB();
				while(i++<forminfo->lvar_size) {
						printf("%d\t", forminfo->used_lvar[i]);
				}
		tabn--;printTAB();printf("]\n");
		printTAB();printf("svar_size=%d\n",forminfo->svar_size);
		printTAB();printf("used_svar=\n");
		printTAB();printf("[\n");tabn++;
				i=0;
				printTAB();
				while(i++<forminfo->svar_size) {
						printf("%d\t", forminfo->used_svar[i]);
				}
		tabn--;printTAB();printf("]\n");

		printTAB();printf("ls_size=%d\n",forminfo->ls_size);
		printTAB();printf("used_pred=\n");
		printTAB();printf("[\n");tabn++;
				i=0;
				printTAB();
				while(i++<forminfo->ls_size) {
						printf("%d\t", forminfo->used_pred[i]);
				}
		tabn--;printTAB();printf("]\n");


		printTAB();printf("fld_size=%d\n",forminfo->fld_size);
		printTAB();printf("used_flds=\n");
		printTAB();printf("[\n");tabn++;
				 i=0;
				printTAB();
				while(i++<forminfo->fld_size) {
						printf("%d\t", forminfo->used_flds[i]);
				}
		tabn--;printTAB();printf("]\n");
		printTAB();printf("pto_size=%d\n",forminfo->pto_size);
		tabn--;	printTAB();printf("}\n");
	}
}



/*typedef struct noll_shom_s
{
  size_t ngraph;                // idx of the negative graph in prob //

  bool is_empty;                // true if no hom found //
  // if false, the elements below are empty //
  // the fields below maps
   * an element from ngraph
   * to one or a set of elements from pgraph //
  uint_t *node_hom;             // node mapping //
  noll_uid_array *pto_hom;      // pto edge mapping //
  noll_graph_array *ls_hom;     // list segment (predicate) edge mapping //

  noll_uid_array *pused;        // edges of pgraph used in this hom
                                 * of size size(noll_prob->pgraph->edges) //
  noll_dform_array *data;       // data constraints generated //
} noll_shom_t;*/
void printShom(noll_shom_t* shom) {
	printTAB();printf("Shom:\n");
	if (shom) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("ngraph=%d\n",shom->ngraph);
		printTAB();printf("is_empty=%d\n",shom->is_empty);
		printTAB();printf("node_hom=\n");
		printTAB();printf("[\n");tabn++;
				int i=0;
				printTAB();
				while(i++<shom->ngraph) {
						printf("%d\t", shom->node_hom[i]);
				}
		tabn--;printTAB();printf("]\n");
		printTAB();printf("pto_hom=\n");
			printNormalArray(shom->pto_hom);
		printTAB();printf("ls_hom=\n");
			printGraphArray(shom->ls_hom);

		printTAB();printf("pused=\n");
			printNormalArray(shom->pused);
		printTAB();printf("data=\n");
			printDformArray(shom->data);

		tabn--;	printTAB();printf("}\n");
	}
}

void printShomArray(noll_shom_array* arr) {
	printTAB();printf("ShomArray: \n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printShom(arr->data_[i]);
				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}


/*typedef struct noll_hom_s
{
  bool is_empty;                true if hom is not found
  if false, the array below is not complete

  noll_shom_array *shom;         array of size ngraph of simple hom
} noll_hom_t; */

void printHom(noll_hom_t* hom) {
	printTAB();printf("Hom:\n");
	if (hom) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("is_empty=%d\n",hom->is_empty);
		printTAB();printf("shom=\n");
			printShomArray(hom->shom);
		tabn--;	printTAB();printf("}\n");
	}
}

void printSatArray(noll_sat_array* arr) {
	printTAB();printf("SatArray: \n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printSat(arr->data_[i]);
				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}


void printLowerMatrix(uid_t **m, int size) {
	printTAB();printf("LowerMatrix:\n");
		if (m) {
			printTAB();printf("[\n");tabn++;
			 for (uint_t i = 0; i <size; i++)
			    {
					printTAB();
				 if (m[i]) {
					   for (uint_t j = 0; j <= i; j++)
								    	  printf("%d\t", m[i][j]);
				 }
			     printf("\n");
			    }
		tabn--;	printTAB();printf("]\n");
		}
}

void printLowerBoolMatrix(_Bool **m, int size) {
	printTAB();printf("LowerBoolMatrix:\n");
		if (m) {
			printTAB();printf("[\n");tabn++;
			 for (uint_t i = 0; i <size; i++)
			    {
				 printTAB();
			      for (uint_t j = 0; j <= i; j++)
			    	  printf("%d\t", m[i][j]);
			     printf("\n");
			    }
		tabn--;	printTAB();printf("]\n");
		}
}
/*typedef struct noll_sat_space_s
{
  noll_space_t *forig;
  union
  {
    uint_t idx;                 // for forig == pto
    struct
    {
      uid_t var;                // UNDEFINED_ID if not apto
      uid_t fld;
    } p;                        // for forig == pred?????s
  } m;
} noll_sat_space_t;*/

void printSatSpace(noll_sat_space_t* satspace) {
	printTAB();printf("SatSpace:\n");
	if (satspace) {
		printTAB();printf("{\n");tabn++;
			printTAB();printf("forig=\n");
				printSpace(satspace->forig);

			printTAB();printf("m={\n");tabn++;
				if (satspace->forig->kind==NOLL_SPACE_PTO) {
						printTAB();printf("idx=%d\n",satspace->m.idx);

				} else if (satspace->forig->kind==NOLL_SPACE_LS) {
					printTAB();printf("p={\n");tabn++;
						printTAB();printf("var=%d\n",satspace->m.p.var);
						printTAB();printf("fld=%d\n",satspace->m.p.fld);
					tabn--;printTAB();printf("}\n");
				}
			tabn--;printTAB();printf("}\n");
		tabn--;	printTAB();printf("}\n");
	}
}


void printSatSpaceArray(noll_sat_space_array* arr) {
	printTAB();printf("SatSpaceArray: \n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printSatSpace(arr->data_[i]);
				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}


/*typedef struct noll_sat_in_s
{
  uid_t x;                       position in locs_array
  uid_t alpha;                   position in slocs_array
} noll_sat_in_t;*/

void printSatIn(noll_sat_in_t* satin) {
	printTAB();printf("SatIn:\n");
	if (satin) {
		printTAB();printf("{\n");tabn++;
			printTAB();printf("x=%d\n",satin->x);
			printTAB();printf("alpha=%d\n",satin->alpha);
		tabn--;	printTAB();printf("}\n");
	}
}


void printSatInArray(noll_sat_in_array* arr) {
	printTAB();printf("SatInArray: \n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printSatIn(arr->data_[i]);
				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}

/*
typedef struct noll_sat_s
{
  noll_form_t *form;            // formula for which the information is stored //
  char *fname;                  // file name used to store the formula //
  FILE *file;                   // if fname already open then != NULL, otherwise == NULL //
  noll_form_info_t *finfo;      // form information used in translation //
  uint_t no_clauses;            // number of clauses put in the file for F_sat //
  uint_t no_vars;               // number of vars used //

  // encoding of constraints [x = y] for any x, y in environment //
  uint_t start_pure;            // id of first variable //
  uint_t size_pure;             // number of boolean variables //
  uint_t size_var_pure;         // number of lines in array below //
  uid_t **var_pure;             // lower diagonal matrix [i][j] j <= i,
                                   storing boolean var id //

  // encoding of points-to atoms [x,f,y] of phi //
  uint_t start_pto;             // id of first variable //
  uint_t size_pto;              // number of variables, size of the array below //
  noll_sat_space_array *var_pto;        // sorted array of pto constraints [x,f,y] //

  // encoding of predicate atoms [P,alpha,x,y,z] in phi //
  uint_t start_pred;            // id of first variable //
  uint_t size_pred;             // number of variables, size of the array below //
  noll_sat_space_array *var_pred;       // sorted array of pred atoms P_alpha(x,y,z) //

  // encoding of anonymous points-to constraints [x,f,alpha]
   // for any x,f,alpha s.t. ty(x)=ty_src(f) in ty_1(alpha), alpha bound in phi //
  uint_t start_apto;            // id of first variable //
  uint_t size_apto;             // number of variables, size of the array below //
  noll_sat_space_array *var_apto;       // sorted array of pto constraints [x,f,alpha] //

  // encoding of sharing atoms [x in alpha] for any x, alpha in phi //
  uint_t start_inset;           // id of first variable //
  uint_t size_inset;            // number of variables, size of the array below //
  noll_sat_in_array *var_inset; // sorted array of sharing atoms x in alpha //

} noll_sat_t;*/
void printSat(noll_sat_t* sat) {
	printTAB();printf("Sat:\n");
	if (sat) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("form=\n");
			printForm(sat->form);
		printTAB();printf("fname=%s\n",sat->fname);
		printTAB();printf("finfo=\n");
			printFormInfo(sat->finfo);
		printTAB();printf("no_clauses=%d\n",sat->no_clauses);
		printTAB();printf("no_vars=%d\n",sat->no_vars);

		printTAB();printf("start_pure=%d\n",sat->start_pure);
		printTAB();printf("size_pure=%d\n",sat->size_pure);
		printTAB();printf("size_var_pure=%d\n",sat->size_var_pure);
		printTAB();printf("var_pure=\n");
				printLowerMatrix(sat->var_pure,sat->size_var_pure);

		printTAB();printf("start_pto=%d\n",sat->start_pto);
		printTAB();printf("size_pto=%d\n",sat->size_pto);
		printTAB();printf("var_pto=\n");
				printSatSpaceArray(sat->var_pto);

		printTAB();printf("start_pred=%d\n",sat->start_pred);
		printTAB();printf("size_pred=%d\n",sat->size_pred);
		printTAB();printf("var_pto=\n");
				printSatSpaceArray(sat->var_pred);

		printTAB();printf("start_apto=%d\n",sat->start_apto);
		printTAB();printf("size_apto=%d\n",sat->size_apto);
		printTAB();printf("var_pto=\n");
				printSatSpaceArray(sat->var_apto);

		printTAB();printf("start_inset=%d\n",sat->start_inset);
		printTAB();printf("size_inset=%d\n",sat->size_inset);
		printTAB();printf("var_pto=\n");
				printSatInArray(sat->var_inset);
		tabn--;	printTAB();printf("}\n");
	}
}


/*  typedef enum noll_logic_t
  {
    NOLL_LOGIC_NOLL,            ESOP'13
    NOLL_LOGIC_SLL,             APLAS'14
    NOLL_LOGIC_SLRD,             SLCOMP'14
    NOLL_LOGIC_SLRDI,
    NOLL_LOGIC_OTHER            NOT SUPPORTED
  } noll_logic_t;*/
char* getEnumLogic(int value) {
	switch(value) {
		case 0:
				return "NOLL_LOGIC_NOLL";
		case 1:
			return "NOLL_LOGIC_SLL";
		case 2:
			return "NOLL_LOGIC_SLRD";
		case 3:
			return "NOLL_LOGIC_SLRDI";
		default:
			return "NOLL_LOGIC_OTHER";
	}
}

/*  typedef enum noll_form_kind_t
  {
    NOLL_FORM_UNSAT = 0, NOLL_FORM_SAT, NOLL_FORM_VALID, NOLL_FORM_OTHER
  } noll_form_kind_t;*/

char* getEnumFormKind(int value) {
	switch(value) {
		case 0:
				return "NOLL_FORM_UNSAT";
		case 1:
			return "NOLL_FORM_SAT";
		case 2:
			return "NOLL_FORM_VALID";
		default:
			return "NOLL_FORM_OTHER";
	}
}

/*typedef struct noll_entl_t
{
  char *smt_fname;              // smt file with entailment
  char *output_fname;           // output file with proof
  noll_logic_t logic;           // theory used in formulas
  noll_form_t *pform;           // positive formula phi
  noll_form_array *nform;       // array of negative formulae psi
  noll_form_kind_t cmd;         // command given: check-sat (default),
  //                check-unsat

  noll_sat_t *pabstr;           // abstraction of the positive formula
  noll_sat_array *nabstr;       // abstraction of the negative formulae

  noll_graph_t *pgraph;         // graph for positive formula
  noll_graph_array *ngraph;     // graphs for negative formulae

  noll_hom_t *hom;              // homomorphism found
} noll_entl_t;*/
void printEntl(noll_entl_t* entl) {
			printTAB();printf("Entl:\n");
			if (entl) {
				printTAB();printf("{\n");tabn++;
					printTAB();printf("smt_fname=%s\n",entl->smt_fname);
					printTAB();printf("output_fname=%s\n",entl->output_fname);
					printTAB();printf("logic=%s\n",getEnumLogic(entl->logic));
					printTAB();printf("pform=\n");
									printForm(entl->pform);
					printTAB();printf("nform=\n");
									printFormArray(entl->nform);
					printTAB();printf("cmd=%s\n",getEnumFormKind(entl->cmd));
					printTAB();printf("pabstr=\n");
									printSat(entl->pabstr);
					printTAB();printf("nabstr=\n");
									printSatArray(entl->nabstr);
					printTAB();printf("pgraph=\n");
									printGraph(entl->pgraph);
					printTAB();printf("ngraph=\n");
									printGraphArray(entl->ngraph);
					printTAB();printf("hom=\n");
									printHom(entl->hom);
				tabn--;	printTAB();printf("}\n");
			}
}



/* Valid term builder in NOLL
  typedef enum
  {
    NOLL_F_FALSE = 0,           boolean operators
    NOLL_F_TRUE,
    NOLL_F_NOT,
    NOLL_F_AND,
    NOLL_F_OR,
    NOLL_F_IMPLIES,
    NOLL_F_EXISTS,
    NOLL_F_FORALL,
    NOLL_F_LVAR,                variable, field, or predicate
    NOLL_F_SVAR,
    NOLL_F_FIELD,
    NOLL_F_PRED,
    NOLL_F_EQ,                   pure operators
    NOLL_F_DISTINCT,
    NOLL_F_ITE,
    NOLL_F_LT,                  Integer theory
    NOLL_F_GT,
    NOLL_F_LE,
    NOLL_F_GE,
    NOLL_F_PLUS,
    NOLL_F_MINUS,
    NOLL_F_INT,                  integer constant
    NOLL_F_DFIELD,               integer field selection
    NOLL_F_BAG,                  Bag_of_Int theory
    NOLL_F_EMPTYBAG,
    NOLL_F_BAGUNION,
    NOLL_F_BAGMINUS,
    NOLL_F_SUBSET,
    NOLL_F_EMP,                 space operators
    NOLL_F_JUNK,
    NOLL_F_WSEP,
    NOLL_F_SSEP,
    NOLL_F_PTO,
    NOLL_F_REF,
    NOLL_F_SREF,
    NOLL_F_INDEX,
    NOLL_F_LOOP,                loop of length at least one
    NOLL_F_SLOC,                share operators
    NOLL_F_UNLOC,
    NOLL_F_INLOC,
    NOLL_F_NILOC,               // not in /
    NOLL_F_EQLOC,
    NOLL_F_LELOC,
    NOLL_F_SELOC,
    NOLL_F_TOBOOL,              // conversion ops /
    NOLL_F_TOSPACE,
    NOLL_F_OTHER
  } noll_expkind_t;*/
char* getEnumExpKind(int value) {
	switch(value) {
		case 0:
				return "NOLL_F_FALSE";
		case 1:
				return "NOLL_F_TRUE";
		case 2:
				return "NOLL_F_NOT";
		case 3:
				return "NOLL_F_AND";
		case 4:
				return "NOLL_F_OR";
		case 5:
				return "NOLL_F_IMPLIES";
		case 6:
				return "NOLL_F_EXISTS";
		case 7:
				return "NOLL_F_FORALL";
		case 8:
				return "NOLL_F_LVAR";
		case 9:
				return "NOLL_F_SVAR";
		case 10:
				return "NOLL_F_FIELD";
		case 11:
				return "NOLL_F_PRED";
		case 12:
				return "NOLL_F_EQ";
		case 13:
				return "NOLL_F_DISTINCT";
		case 14:
				return "NOLL_F_ITE";
		case 15:
				return "NOLL_F_LT";
		case 16:
				return "NOLL_F_GT";
		case 17:
				return "NOLL_F_LE";
		case 18:
				return "NOLL_F_GE";
		case 19:
				return "NOLL_F_PLUS";
		case 20:
				return "NOLL_F_MINUS";
		case 21:
				return "NOLL_F_INT";
		case 22:
				return "NOLL_F_DFIELD";
		case 23:
				return "NOLL_F_BAG";
		case 24:
				return "NOLL_F_EMPTYBAG";
		case 25:
				return "NOLL_F_BAGUNION";
		case 26:
				return "NOLL_F_BAGMINUS";
		case 27:
				return "NOLL_F_SUBSET";
		case 28:
				return "NOLL_F_EMP";
		case 29:
				return "NOLL_F_JUNK";
		case 30:
				return "NOLL_F_WSEP";
		case 31:
				return "NOLL_F_SSEP";
		case 32:
				return "NOLL_F_PTO";
		case 33:
				return "NOLL_F_REF";
		case 34:
			return "NOLL_F_SREF";
		case 35:
			return "NOLL_F_INDEX";
		case 36:
			return "NOLL_F_LOOP";
		case 37:
			return "NOLL_F_SLOC";
		case 38:
			return "NOLL_F_UNLOC";
		case 39:
			return "NOLL_F_INLOC";
		case 40:
			return "NOLL_F_NILOC";
		case 41:
			return "NOLL_F_EQLOC";
		case 42:
			return "NOLL_F_LELOC";
		case 43:
			return "NOLL_F_SELOC";
		case 44:
			return "NOLL_F_TOBOOL";
		case 45:
			return "NOLL_F_TOSPACE";
		default:
			return "NOLL_F_OTHER";
	}
}

/*typedef struct noll_exp_t
  {
    noll_expkind_t discr;

    union
    {
      uint_t sid;

      long value;

      struct
      {
        noll_var_array *lvars;
        uint_t lstart;
        uint_t lend;
        noll_var_array *svars;
        uint_t sstart;
        uint_t send;
      } quant;

    } p;

    struct noll_exp_t **args;   //array of expression args or NULL
    uint_t size;

  } noll_exp_t;
 * */
void printExp(noll_exp_t* exp) {
	printTAB();printf("Exp:\n");
	if (exp) {
		printTAB();printf("{\n");tabn++;
				printTAB();printf("discr (kind)=%s\n",getEnumExpKind(exp->discr));
				printTAB();printf("p={\n");tabn++;
					if (exp->discr>=8&&exp->discr<=10) {
						printTAB();printf("sid=%d\n",exp->p.sid);
					} else if (exp->discr==21) {
						printTAB();printf("value=%ld\n",exp->p.value);
					} else if (exp->discr==7||exp->discr==6){
						printTAB();printf("{\n");tabn++;
								printTAB();printf("lvars=:\n");
									printVarArray(exp->p.quant.lvars);
								printTAB();printf("lstart=%d\n",exp->p.quant.lstart);
								printTAB();printf("lend=%d\n",exp->p.quant.lend);
								printTAB();printf("svars=:\n");
									printVarArray(exp->p.quant.svars);
								printTAB();printf("sstart=%d\n",exp->p.quant.sstart);
								printTAB();printf("send=%d\n",exp->p.quant.send);
								tabn--;printTAB();printf("}\n");
					}
					tabn--;printTAB();printf("}\n");
				if (exp->args) {
					printTAB();printf("\tsize=%d\n",exp->size);
					printTAB();printf("args=[\n");
						int i=0;
						for (;i<exp->size;i++) {
							printExp(exp->args[i]);
						}
						printTAB();printf("]\n");
				} else {
					printTAB();printf("args:NULL\n");
				}
				tabn--;printTAB();printf("}\n");
	}
}




/*  typedef struct noll_ls_t
  {
    uid_t pid;                  // predicate
    noll_uid_array *args;       // arguments used
    uid_t sid;                  // set of locations variable bound
    bool is_loop;               // set if it is a loop instance
  } noll_ls_t;
 * */
void printLs(noll_ls_t* ls) {
	printTAB();printf("Ls:\n");
	if (ls) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("pid=%d\n",ls->pid);
		printTAB();printf("args=\n");
						printNormalArray(ls->args);
					printTAB();printf("sid=%d\n",ls->sid);
					printTAB();printf("is_loop=%d\n",ls->is_loop);
					tabn--;printTAB();printf("}\n");
	}
}

/*  typedef struct noll_pto_t
  {
    uid_t sid;                  // source location
    noll_uid_array *fields;     // array of fields
    noll_uid_array *dest;       // array of destination locations
  } noll_pto_t;*/
void printPto(noll_pto_t* pto) {
	printTAB();printf("Pto:\n");
	if (pto) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("sid=%d\n",pto->sid);
		printTAB();printf("fields=\n");
						printNormalArray(pto->fields);
					printTAB();printf("dest=\n");
						printNormalArray(pto->dest);
					tabn--;	printTAB();printf("}\n");
	}
}






/*  typedef enum noll_space_op_t
  {
    NOLL_SPACE_EMP = 0,
    NOLL_SPACE_JUNK,
    NOLL_SPACE_PTO,
    NOLL_SPACE_LS,
    NOLL_SPACE_WSEP,
    NOLL_SPACE_SSEP,
    NOLL_SPACE_OTHER
  } noll_space_op_t;*/
char* getEnumSpaceOp(int value) {
	switch(value) {
		case 0:
				return "NOLL_SPACE_EMP";
		case 1:
			return "NOLL_SPACE_JUNK";
		case 2:
			return "NOLL_SPACE_PTO";
		case 3:
			return "NOLL_SPACE_LS";
		case 4:
			return "NOLL_SPACE_WSEP";
		case 5:
			return "NOLL_SPACE_SSEP";
		default:
			return "NOLL_PRED_OTHER";
	}
}


void printSpaceArray(noll_space_array* arr)  {
	printTAB();printf("SpaceArray:\n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
						printSpace(arr->data_[i]);
						printTAB();printf("\n");
			}
			tabn--;printTAB();printf("]\n");
	}
}

/*struct noll_space_s
  {
    noll_space_op_t kind;
    bool is_precise;

    union
    {
      noll_pto_t pto;           // points-to constraint
      noll_ls_t ls;             // list segment constraint
      noll_space_array *sep;    // array of constraints
      // for weak or strong separation
    } m;
  };
 * */

void printSpace(noll_space_t* space) {
	printTAB();printf("Space:\n");
	if (space) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("kind=%s\n",getEnumSpaceOp(space->kind));
		printTAB();printf("\tsize=%d\n",space->is_precise);
		printTAB();printf("m={\n");tabn++;
						if (space->kind==2) {
							printTAB();printPto(&space->m.pto);
						} else if (space->kind==3) {
							printTAB();printLs(&space->m.ls);
						} else {
							printTAB();printSpaceArray(space->m.sep);
						}
						tabn--;printTAB();printf("}\n");
					tabn--;	printTAB();printf("}\n");
	}
}


/*  typedef enum noll_pure_op_t
  {
    NOLL_PURE_EQ = 0, NOLL_PURE_NEQ, NOLL_PURE_OTHER
  } noll_pure_op_t;*/
char* getEnumPuerOp(int value) {
	 switch(value) {
	 		case 0:
	 				return "NOLL_PURE_EQ";
	 		case 1:
	 			return "NOLL_PURE_NEQ";
	 		default:
	 			return "NOLL_PURE_OTHER";
	 	}
}

void printUpperMatrix(noll_pure_op_t ** m, uint_t size) {
	printTAB();printf("Matrix:\n");
	if (m) {
		printTAB();printf("[\n");tabn++;
		int i=0;
		int j=0;
		for (;i<size;i++) {
			printTAB();printf("\t");
			j=0;
			for(;j<size-i;j++) {
				printf("%s\t", getEnumPuerOp(m[i][j]));
			}
			printf("\n");
		}
	tabn--;	printTAB();printf("]\n");
	}
}

/*  typedef struct noll_pure_t
  {
    noll_pure_op_t **m;         // matrix of equality and inequality constraints
    uint_t size;                // allocated size for the matrix, 0 if empty or == locs_array size
    noll_dform_array *data;     // set (conjunction of) pure constraints on data
  } noll_pure_t;*/
void printPure(noll_pure_t* pure) {
	printTAB();printf("Pure:\n");
	if (pure) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("m=\n");
						printUpperMatrix(pure->m,pure->size);
						printTAB();printf("\tsize=%d\n",pure->size);
						printTAB();printf("data=\n");
					printDformArray(pure->data);
				tabn--;	printTAB();printf("}\n");
	}
}


/*
 * typedef struct noll_pred_rule_t
  {
    noll_var_array *vars;       // nil + formal arguments + existentially quantified variables
    uint_t fargs;               // limit of formal arguments
    noll_pure_t *pure;          // pure part of the rule (including data)
    noll_space_t *pto;          // points-to part, if any, NULL for base rules
    noll_space_t *nst;          // calls to predicates, non-recursive, NULL for base rule
    noll_space_t *rec;          // recursive calls
  } noll_pred_rule_t;
 * */

void printPredRule(noll_pred_rule_t* predrule) {
	printTAB();printf("PredRule:\n");
	if (predrule) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("vars=\n");
							printVarArray(predrule->vars);
			printTAB();printf("fargs=%d\n",predrule->fargs);
			printTAB();	printf("pure=\n");
					printPure(predrule->pure);
			printTAB();	printf("pto=\n");
					printSpace(predrule->pto);
			printTAB();printf("rec=\n");
					printSpace(predrule->rec);
		tabn--;	printTAB();printf("}\n");
	}
}
/* typedef enum
  {
    NOLL_TYP_BOOL = 0,
    NOLL_TYP_INT,
    NOLL_TYP_BAGINT,
    NOLL_TYP_RECORD,
    NOLL_TYP_SETLOC,
    NOLL_TYP_FIELD,
    NOLL_TYP_SETREF,
    NOLL_TYP_SPACE,
    NOLL_TYP_OTHER
  } noll_typ_t;*/
char * getEnumTyp(int value) {
	 switch(value) {
	 		case 0:
	 				return "NOLL_TYP_BOOL";
	 		case 1:
	 			return "NOLL_TYP_INT";
	 		case 2:
	 			return "NOLL_TYP_BAGINT";
	 		case 3:
	 			return "NOLL_TYP_RECORD";
	 		case 4:
	 			return "NOLL_TYP_SETLOC";
	 		case 5:
	 			return "NOLL_TYP_FIELD";
	 		case 6:
	 			return "NOLL_TYP_SETREF";
	 		case 7:
	 			return "NOLL_TYP_SPACE";
	 		default:
	 			return "NOLL_TYP_OTHER";
	 	}
}

 /*  typedef enum
  {
    NOLL_SCOPE_LOCAL = 0, NOLL_SCOPE_GLOBAL, NOLL_SCOPE_OTHER
  } noll_scope_e;
  * */
 char* getEnumScope(int value) {
	 switch(value) {
	 		case 0:
	 				return "NOLL_SCOPE_LOCAL";
	 		case 1:
	 			return "NOLL_SCOPE_GLOBAL";
	 		default:
	 			return "NOLL_SCOPE_OTHER";
	 	}
 }

 /*
  *   typedef struct noll_type_t
  {
    noll_typ_t kind;
    noll_uid_array *args;       // type arguments, including the record index
  } noll_type_t;
  * */
void printType(noll_type_t* type ){
	printTAB();printf("Type:\n");
	if (type) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("kind=%s\n",getEnumTyp(type->kind));
		printTAB();printf("args=\n");
					printNormalArray(type->args);
		tabn--;printTAB();printf("}\n");
		}
}

/**
 *   typedef struct noll_var_t
  {
    char *vname;                // declaration name
    uid_t vid;                  // variable identifier
    noll_type_t *vty;           // type
    noll_scope_e scope;         // visibility
  } noll_var_t;
 */
void printVar(noll_var_t* var) {
	printTAB();printf("Var:\n");
	if (var) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("vname=%s\n",var->vname);
		printTAB();printf("vid=%d\n",var->vid);
		printTAB();printf("vty=\n");
						printType(var->vty);
		printTAB();printf("scope=%s\n",getEnumScope(var->scope));
		tabn--;printTAB();printf("}\n");
		}
}


void printPredRuleArray(noll_pred_rule_array* arr) {
	printTAB();printf("PredRuleArray:\n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
						printPredRule(arr->data_[i]);
				printTAB();printf("\n");
			}
			tabn--;printTAB();printf("]\n");
	}
}
void printVarArray(noll_var_array* arr) {
	printTAB();printf("VarArray:\n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printVar(arr->data_[i]);
				printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}
/*
 * typedef struct noll_pred_binding_t
  {
    size_t pargs;               // type of list = number of arguments of this record type 2 or 4
    noll_var_array *vars;       // nil + formal arguments (+ old: local variables for sigma_0, sigma_1)
    uint_t fargs;               // number of formal arguments in the array above
    noll_space_t *sigma_0;      // old: points-to part
    noll_space_t *sigma_1;      // old: nested part
    noll_pred_rule_array *base_rules;   // set of base rules
    noll_pred_rule_array *rec_rules;    // set of base rules
  } noll_pred_binding_t;
 *
 */
void printPredBinding(noll_pred_binding_t* def) {
	printTAB();printf("PredBinding:\n");
	if (def) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("pargs=%d\n",def->pargs);
		printTAB();printf("vars={\n");
					printVarArray(def->vars);
		printTAB();	printf("fargs=%d\n",def->fargs);
		printTAB();printf("base_rules=\n");
					printPredRuleArray(def->base_rules);
		printTAB();printf("rec_rules=\n");
					printPredRuleArray(def->rec_rules);
	tabn--;	printTAB();printf("}\n");
		}
}


/*
 *   typedef enum
  {
    NOLL_PRED_LST_PAR,          // list-like definition, with parent
    NOLL_PRED_LST,              // list-like definition, one way
    NOLL_PRED_COMP_PAR,         // compositional definition, with parent
    NOLL_PRED_COMP,             // compositional definition, one way
    NOLL_PRED_WS,               // well structured definition
    NOLL_PRED_OTHER             // default
  } noll_pred_kind_e;
 * */
char* getEnumPredKind(int value) {
	switch(value) {
		case 0:
				return "NOLL_PRED_LST_PAR";
		case 1:
			return "NOLL_PRED_LST";
		case 2:
			return "NOLL_PRED_COMP_PAR";
		case 3:
			return "NOLL_PRED_COMP";
		case 4:
			return "NOLL_PRED_WS";
		default:
			return "NOLL_PRED_OTHER";
	}
}
/*
 * typedef struct noll_pred_typing_t
  {
    uid_t ptype0;
    noll_uint_array *ptypes;
    noll_uint_array *pfields;
    noll_pred_kind_e pkind;
    bool isUnaryLoc;
    bool useNil;
    bool isTwoDir;
    noll_uid_array *argkind;

    noll_uint_array *ppreds;
  } noll_pred_typing_t;
 * */
void printPredTyping(noll_pred_typing_t* typ) {
	printTAB();printf("PredTyping:\n");
	if (typ) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("ptyp0=%d\n",typ->ptype0);
		printTAB();printf("ptypes=\n");
				printNormalArray(typ->ptypes);
		printTAB();printf("pfields=\n");
				printNormalArray(typ->pfields);
		printTAB();printf("pkind=%s\n",getEnumPredKind(typ->pkind));
		printTAB();printf("isUnaryLoc=%d\n",(typ->isUnaryLoc));
		printTAB();printf("useNil=%d\n",(typ->useNil));
		printTAB();printf("isTwoDir=%d\n",(typ->isTwoDir));
		printTAB();printf("argkind=\n");
				printNormalArray(typ->argkind);
		printTAB();printf("ppreds=\n");
				printNormalArray(typ->ppreds);
		tabn--;printTAB();printf("}\n");
	}
}


/*
 *   typedef struct noll_pred_t
  {
    char *pname;                // declaration name
    uid_t pid;                  // predicate identifier
    noll_pred_binding_t *def;   // predicate definition
    noll_pred_typing_t *typ;    // predicate typing infos
  } noll_pred_t;
 * */
void printPred(noll_pred_t* pred) {
	printTAB();printf("Pred\n");
	if (pred) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("pname=%s\n",pred->pname);
		printTAB();printf("pid=%d\n",pred->pid);
		printTAB();printf("def=\n");
				printPredBinding(pred->def);
		printTAB();printf("typ=\n");
				printPredTyping(pred->typ);
	tabn--;	printTAB();printf("}\n");
	}
}

void printPredArray(noll_pred_array* arr) {
	printTAB();printf("PredArray:\n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
				printPred(arr->data_[i]);
				printf("\n");
			}
	tabn--;		printTAB();printf("]\n");
	}
}



/*
/// Enumeration of possible aliasing of nodes
enum noll_tree_label_type_t
{
  NOLL_TREE_LABEL_ALLOCATED,    ///< the node is allocated: no aliasing is used
  NOLL_TREE_LABEL_ALIASING_VARIABLE,    ///< a node with a program variable is aliased
  NOLL_TREE_LABEL_ALIASING_MARKING,     ///< marking is used as the relation
  NOLL_TREE_LABEL_HIGHER_PRED,  ///< higher-order predicate
};
*/
char* getEnumTreeLabelType( int value) {
	switch(value) {
			case 0:
				return "NOLL_TREE_LABEL_ALLOCATED";
			case 1:
				return "NOLL_TREE_LABEL_ALIASING_VARIABLE";
			case 2:
				return "NOLL_TREE_LABEL_ALIASING_MARKING";
			case 3:
				return "NOLL_TREE_LABEL_HIGHER_PRED";
			default:
				return "NOLL_TREE_LABEL_OTHER";
		}
}

void printTaSymbolArray(noll_ta_symbol_array* arr) {
	printTAB();printf("TaSymbolArray:\n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
				printTaSymbol(arr->data_[i]);
				printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
		}
}

/*
 * typedef struct noll_ta_symbol
{
  /// The type of the label (see enum @p noll_tree_label_type_t)
  unsigned char label_type;

  union
  {
    /// The structure used for allocated nodes (for label_type ==
    /// NOLL_TREE_LABEL_ALLOCATED)
    struct
    {
      /// The selectors
      noll_uid_array *sels;

      /// Variables that might alias with the node
      noll_uid_array *vars;

      /// The (least) marking of the node
      noll_uid_array *marking;
    } allocated;

    /// Marking of the aliased node (for label_type ==
    /// NOLL_TREE_LABEL_ALIASING_MARKING)
    struct
    {
      /// The marking
      noll_uid_array *marking;

      /// Identifier of the relation (of the type noll_alias_marking_rel_t)
      unsigned char id_relation;
    } alias_marking;

    /// Name of the variable the node is aliased to (for label_type ==
    /// NOLL_TREE_LABEL_ALIASING_VARIABLE)
    uid_t alias_var;

    /// Higher-order predicate (for label_type == NOLL_TREE_LABEL_HIGHER_PRED)
    struct
    {
      /// the higher-order predicate represented by the symbol
      const noll_pred_t *pred;

      /// Variables that might alias with the node
      noll_uid_array *vars;

      /// The (least) marking of the node
      noll_uid_array *marking;
    } higher_pred;
  };

  /// The string representation (for humans)
  char *str;
} noll_ta_symbol_t;
 * */

void printTaSymbol(const noll_ta_symbol_t*  sym) {
	printTAB();printf("TaSymbol:\n");
	if (sym) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("label_type=%s,\n",getEnumTreeLabelType(sym->label_type));
		printTAB();printf("str=%s,\n",sym->str);
		printTAB();printf("p={\n");tabn++;
					if (sym->label_type==0) {
						printTAB();printf("sels=\n");
							printNormalArray(sym->allocated.sels);
							printTAB();printf("vars=\n");
								printNormalArray(sym->allocated.vars);
							printTAB();printf("markings=\n");
										printNormalArray(sym->allocated.marking);

					} else if (sym->label_type==1) {
						printTAB();printf("alias_var=%d\n",sym->alias_var);
					} else if (sym->label_type==2) {
						printTAB();printf("marking=\n");
							printNormalArray(sym->alias_marking.marking);
						printTAB();printf("id_relation=%d\n",sym->alias_marking.id_relation);

					} else {
						printTAB();printf("pred=\n");
							printPred(sym->higher_pred.pred);
						printTAB();printf("vars=\n");
							printNormalArray(sym->higher_pred.vars);
						printTAB();printf("marking=\n");
							printNormalArray(sym->higher_pred.marking);
					}
		tabn--;	printTAB();printf("}");
	tabn--;	printTAB();printf("}");
	}
}

void printNormalArray(noll_uid_array* arr) {
		if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);tabn++;
			printTAB();printf("[");
			for(;i<arr->size_;i++) {
				printf("%d,\t", arr->data_[i]);
			}
			printf("]\n");tabn--;
		}
}



/*
typedef enum noll_data_op_t
  {
    NOLL_DATA_INT = 0,
    NOLL_DATA_VAR,
    NOLL_DATA_EMPTYBAG,
    NOLL_DATA_FIELD,
    NOLL_DATA_EQ,
    NOLL_DATA_NEQ,
    NOLL_DATA_ITE,
    NOLL_DATA_LT,
    NOLL_DATA_GT,
    NOLL_DATA_LE,
    NOLL_DATA_GE,
    NOLL_DATA_PLUS,
    NOLL_DATA_MINUS,
    NOLL_DATA_BAG,
    NOLL_DATA_BAGUNION,
    NOLL_DATA_BAGMINUS,
    NOLL_DATA_SUBSET,
    NOLL_DATA_IMPLIES,
    NOLL_DATA_OTHER            
  } noll_data_op_t;
*/

char* getEnumDataOp(int value) {
	switch(value) {
		case 0:
			return "NOLL_DATA_EQ";
		case 1:
			return "NOLL_DATA_LT";
		case 2:
			return "NOLL_DATA_GT";
		case 3:
			return "NOLL_DATA_LE";
		case 4:
			return "NOLL_DATA_GE";
		case 5:
			return "NOLL_DATA_NEQ";
		case 6:
			return "NOLL_DATA_PLUS";
		case 7:
			return "NOLL_DATA_MINUS";
		case 8:
			return "NOLL_DATA_ITE";
		case 9:
			return "NOLL_DATA_INT";
		case 10:
			return "NOLL_DATA_VAR";
		case 11:
			return "NOLL_DATA_EMPTYBAG";
		case 12:
			return "NOLL_DATA_FIELD";
		case 13:
			return "NOLL_DATA_BAG";
		case 14:
			return "NOLL_DATA_BAGUNION";
		case 15:
			return "NOLL_DATA_BAGMINUS";
		case 16:
			return "NOLL_DATA_SUBSET";
		case 17:
			return "NOLL_DATA_IMPLIES";
		default:
			return "NOLL_DATA_OTHER";
	}
} 

void printDtermArray(noll_dterm_array* arr) {
	printTAB();printf("DtermArray: \n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();	printf("index=%d:\n",i);
					printDterm(arr->data_[i]);
				printf("\n");
			}
	tabn--;		printTAB();	printf("]\n");
	}
}

/*
struct noll_dterm_s
  {
    noll_data_op_t kind;        // only data terms
    noll_typ_t typ;             // either NOLL_TYP_INT or NOLL_TYP_BAGINT

    union
    {
      long value;               // integer constant
      uid_t sid;                // symbol (variable or field) identifier
      noll_dform_t *cond;       // simple condition for ite
    } p;

    noll_dterm_array *args;     // NULL for 0-arity terms
  };
*/

void printDterm(noll_dterm_t* dterm) {
	printTAB();printf("Dterm:\n");
		if (dterm) {
			printTAB();printf("{\n");tabn++;
			printTAB();printf("\tkind=%s,\n",getEnumDataOp(dterm->kind));
			printTAB();printf("\ttyp=%s,\n",getEnumTyp(dterm->typ));
			printTAB();	printf("p={\n");tabn++;
						if (dterm->kind==NOLL_DATA_INT) {
							printTAB();printf("\tvalue=%ld\n", dterm->p.value);
						}else if (dterm->kind==NOLL_DATA_VAR||dterm->kind==NOLL_DATA_FIELD) {
							printTAB();printf("\tsid=%d\n",dterm->p.sid);
						} else if (dterm->kind>=NOLL_DATA_SUBSET) {

						} else {
							if (dterm->kind>=NOLL_DATA_EQ&&dterm->kind<=NOLL_DATA_NEQ) {
								printDform(dterm->p.cond);
							}
							printDtermArray(dterm->args);
						}
			tabn--;	printTAB();printf("}\n");
	tabn--;		printTAB();printf("}\n");
		}
}

void printDformArray(noll_dform_array* arr) {
	printTAB();printf("DformArray: \n");
	if (arr) {
			int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printDform(arr->data_[i]);
				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}
/*
  struct noll_dform_s
  {
    noll_data_op_t kind;        // only data formulas
    noll_typ_t typ;             // either NOLL_TYP_INT or NOLL_TYP_BAGINT

    union
    {
      noll_dterm_array *targs;  // term arguments
      noll_dform_array *bargs;  // boolean arguments iff kind == NOLL_DATA_IMPLIES
    } p;
  };

*/
void printDform(noll_dform_t* dform) {
	printTAB();printf("Dform\n");
	if (dform) {
		printTAB();printf("{\n");tabn++;
		printTAB();printf("\tkind=%s,\n",getEnumDataOp(dform->kind));
		printTAB();printf("\ttyp=%s,\n",getEnumTyp(dform->typ));
		printTAB();printf("\tp={\n");tabn++;
					if (dform->kind==NOLL_DATA_IMPLIES) {
						printDformArray(dform->p.bargs);
					} else  {
						printDtermArray(dform->p.targs);
					}
	tabn--;	printTAB();printf("}\n");
	tabn--;	printTAB();printf("}\n");
	}
}

