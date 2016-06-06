#include "noll_form.h"
#include "noll.h"
#include <stdio.h>
#include "slid_sat.h"


unsigned int tabn=0;



void printLowerBoolMatrix(_Bool **m, int size) ;
void printDtermArray(noll_dterm_array* dterms);
void printDterm(noll_dterm_t* dterm);
void printDformArray(noll_dform_array* dforms);
void printDform(noll_dform_t* dform);
char* getEnumTyp(int value);
char* getEnumDataOp(int value);
//char* getEnumTreeLabelType(int value);
void printNormalArray( noll_uid_array* arr);
//void printTaSymbolArray(noll_ta_symbol_array* arr );
//void printTaSymbol(const noll_ta_symbol_t* arr);
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
void printTAB(void);
char* getEnumEdgeKind(int value) ;
void printEntl(noll_entl_t* entl);
char* getEnumLogic(int value);
char* getEnumFormKind(int value);
//void printSat(noll_sat_t* sat) ;
//void printSatArray(noll_sat_array* arr) ;
//void printHom(noll_hom_t* hom);
void printMatrix(noll_uid_array** m, int size) ;
void printRMatrix(noll_uid_array** m, int size) ;
void printAstMatrix(Z3_context c, Z3_ast **m, int row, int col) ;
//void printShomArray(noll_shom_array* arr) ;

//void printShom(noll_shom_t* shom);
//void printFormInfo(noll_form_info_t* forminfo);
void printForm(noll_form_t* form);
void printFormArray(noll_form_array* arr) ;
void printShareArray(noll_share_array* arr) ;
void printShare(noll_atom_share_t* share) ;
char* getEnumShareOp(int value);
//void printEdgeArray(noll_edge_array* arr) ;

//void printSatSpaceArray(noll_sat_space_array* arr) ;
//void printSatSpace(noll_sat_space_t* satspace) ;
void printLowerMatrix(uid_t **var_pure, int size) ;
void printStermArray(noll_sterm_array* arr) ;
void printSterm(noll_sterm_t* sterm) ;
char* getEnumStermKind(int value) ;
void printArgKind(noll_uid_array* arr) ;

//void printGraphArray(noll_graph_array* arr) ;
//
//void printGraph(noll_graph_t* graph);
//
//void printEdge(noll_edge_t* edge);
//void printSatIn(noll_sat_in_t* satin) ;
//void printSatInArray(noll_sat_in_array* arr) ;
void printRecordArray(noll_record_array* arr) ;
void printRecord(noll_record_t* record);
void printFieldArray(noll_field_array* arr) ;
void printField(noll_field_t* field) ;
char* getEnumFieldKind(int value) ;

void printDataConstr(slid_data_constr* data);
void printSlidContext(Z3_context c,_slid_context* slid ) ;
void printAstArray(Z3_context c, z3_ast_array* arr) ;

void printAst(Z3_context c, Z3_ast ast);
void printAlloc(Z3_context c, slid_in_alloc_loc* loc) ;
void printAllocArray(Z3_context c, slid_in_alloc_loc_array* arr) ;
void printAllocArrays(Z3_context c, slid_in_alloc_loc_arrays* arr) ;




char* getEnumSlidSat(int value) ;
char* getEnumAtype(int value) ;


void printAllocArrays(Z3_context c, slid_in_alloc_loc_arrays* arr) {
	printTAB();printf("LocationArrays: \n");
	if (arr) {
			unsigned int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					printAllocArray(c,arr->data_[i]);
				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}

void printAllocArray(Z3_context c, slid_in_alloc_loc_array* arr)  {
	printTAB();printf("LocationArray: \n");
	if (arr) {
			unsigned int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[");
			for(;i<arr->size_;i++) {
					printAlloc(c,arr->data_[i]);
				printf("  ,  ");
			}
			printTAB();printf("]\n");
	}
}

/*//interest allocate location
typedef struct{
	int sid;     //variable id
	Z3_ast bvar;   //boolean variable
}slid_in_alloc_loc;*/

void printAlloc(Z3_context c, slid_in_alloc_loc* loc) {
		if (loc) {
			printf("{");
				 printf("sid=%d,",loc->sid);
				 printf("bvar=%s",Z3_ast_to_string(c,loc->bvar));
			printf("}");
		}
}

/* typedef enum
  {
    NOLL_ATYP_LROOT = 0,
    NOLL_ATYP_LPAR,
    NOLL_ATYP_BROOT,
    NOLL_ATYP_IROOT,
    NOLL_ATYP_LPENDING,
    NOLL_ATYP_LLST,
    NOLL_ATYP_BPENDING,
    NOLL_ATYP_IPENDING,
    NOLL_ATYP_BORDER,
    NOLL_ATYP_OTHER
  } noll_atyp_e;*/
char* getEnumAtype(int value)  {
	switch(value) {
	  		case 0:
	  			return "NOLL_ATYP_LROOT";
	  		case 1:
	  			return "NOLL_ATYP_LPAR";
	  		case 2:
	  			return "NOLL_ATYP_BROOT";
	  		case 3:
	  			return "NOLL_ATYP_IROOT";
	  		case 4:
	  			return "NOLL_ATYP_LPENDING";
	  		case 5:
	  			return "NOLL_ATYP_LLST";
	  		case 6:
	  			return "NOLL_ATYP_BPENDING";
	  		case 7:
	  			return "NOLL_ATYP_IPENDING";
	  		case 8:
	  			return "NOLL_ATYP_BORDER";
	  		default:
	  			return "NOLL_ATYP_OTHER";
	  	}
}
void printAst(Z3_context c, Z3_ast ast) {
	printTAB();printf("Ast:\n");
		if (ast) {
			printTAB();printf("{\n");tabn++;
			Z3_set_ast_print_mode(c,0);
				printTAB(); printf("%s\n",Z3_ast_to_string(c,ast));
			tabn--;	printTAB();printf("}\n");
		}
}

/*typedef enum{
	SLID_UNSAT = 0,
	SLID_SAT,
	SLID_UNDEF
}slid_sat_t;*/
char* getEnumSlidSat(int value) {
  	switch(value) {
  		case 0:
  			return "SLID_UNSAT";
  		case 1:
  			return "SLID_SAT";
  		default:
  			return "SLID_UNDEF";
  	}
}

/*typedef struct{
	int sid;
	noll_dform_array *ce;
	noll_dform_t *cl;
	noll_dform_t *cg;
	noll_dform_array *stc;
	noll_dform_array *trans;
}slid_data_constr;*/
void printDataConstr(slid_data_constr* data) {
	printTAB();printf("DataConstr:\n");
	if (data) {
		printTAB();printf("{\n");tabn++;
			printTAB();printf("sid=%d\n",data->sid);
			printTAB();printf("ce=\n");
					printDformArray(data->ce);
			printTAB();printf("cl=\n");
					printDform(data->cl);
			printTAB();printf("cg=\n");
					printDform(data->cg);
			printTAB();printf("stc=\n");
					printDformArray(data->stc);
			printTAB();printf("trans=\n");
					printDformArray(data->trans);
		tabn--;	printTAB();printf("}\n");
	}
}



void printAstArray(Z3_context c, z3_ast_array* arr) {
	printTAB();printf("AstArray: \n");
	if (arr) {
			unsigned int i=0;
			printTAB();printf("size=%d\n", arr->size_);
			printTAB();printf("[\n");tabn++;
			for(;i<arr->size_;i++) {
				printTAB();printf("index=%d:\n",i);
					if (arr->data_[i]) {
						printTAB();printf("%s", Z3_ast_to_string(c, arr->data_[i]));
					} else {
						printTAB();printf("NULL");
					}

				printTAB();printf("\n");
			}
		tabn--;	printTAB();printf("]\n");
	}
}


void printAstMatrix(Z3_context c, Z3_ast **m, int row, int col) {
	printTAB();printf("AstMatrix:\n");
			if (m) {
				printTAB();printf("[\n");tabn++;
				 for (uint_t vi = 0; vi < (unsigned int)row; vi++)
				    {
				      if (m[vi] != NULL)
				        {
				    	  printTAB();
				          for (uint_t i = 0; i < (unsigned int)col; i++)
				        	  printf ("%s\t",Z3_ast_to_string(c, m[vi][i]));
				        }
				      printf("\n");
				    }
				 tabn--;printTAB();printf("]\n");
			}
}

/*typedef struct{
	z3_ast_array *var;          //nil + variables in the formula
	z3_ast_array *k;            //times unfolding the predicates
	noll_space_array *space;    //spatial part of the formula
	Z3_ast **m;                 //matrix of bool variables
	Z3_sort int_sort, bool_sort;//sort used
	unsigned int nLoc;
	Z3_ast abstr;
	slid_sat_t sat_type;
}_slid_context;*/

void printSlidContext( Z3_context c,_slid_context* slid) {
	Z3_set_ast_print_mode(c,Z3_PRINT_SMTLIB_FULL);
	printTAB();printf("SlidContext:\n");
	if (slid) {
		printTAB();printf("{\n");tabn++;
			printTAB();printf("var=\n");
						printAstArray(c,slid->var);
			printTAB();printf("k=\n");
						printAstArray(c,slid->k);
			printTAB();printf("space=\n");
						printSpaceArray(slid->space);
			printTAB();printf("m=\n");
						printAllocArrays(c,slid->m);
			printTAB();printf("abstr=\n%s\n",Z3_ast_to_string(c, slid->abstr));
			printTAB();printf("nLoc=%d\n",slid->nLoc);
			printTAB();printf("int_sort=%s\n",Z3_sort_to_string(c, slid->int_sort));
			printTAB();printf("bool_sort=%s\n",Z3_sort_to_string(c, slid->bool_sort));
			printTAB();printf("sat_type=%s\n",getEnumSlidSat(slid->sat_type));

		tabn--;	printTAB();printf("}\n");
	}
}


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
			unsigned int i=0;
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
			unsigned int i=0;
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



void printTAB(void) {
	unsigned int i=0;
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



void printMatrix(noll_uid_array** m, int size) {
	printTAB();printf("Matrix:\n");
		if (m) {
			printTAB();printf("[\n");tabn++;
			 for (uint_t vi = 0; vi <(unsigned int) size; vi++)
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
			 for (uint_t vi = 0; vi <(unsigned int) size; vi++)
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
			unsigned int i=0;
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
			unsigned int i=0;
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
			unsigned int i=0;
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




void printLowerMatrix(uid_t **m, int size) {
	printTAB();printf("LowerMatrix:\n");
		if (m) {
			printTAB();printf("[\n");tabn++;
			 for (uint_t i = 0; i <(unsigned int)size; i++)
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
			 for (uint_t i = 0; i <(unsigned int)size; i++)
			    {
				 printTAB();
			      for (uint_t j = 0; j <= i; j++)
			    	  printf("%d\t", m[i][j]);
			     printf("\n");
			    }
		tabn--;	printTAB();printf("]\n");
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
//					printTAB();printf("pabstr=\n");
//									printSat(entl->pabstr);
//					printTAB();printf("nabstr=\n");
//									printSatArray(entl->nabstr);
//					printTAB();printf("pgraph=\n");
//									printGraph(entl->pgraph);
//					printTAB();printf("ngraph=\n");
//									printGraphArray(entl->ngraph);
//					printTAB();printf("hom=\n");
//									printHom(entl->hom);
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
						unsigned int i=0;
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
			unsigned int i=0;
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
							printPto(&space->m.pto);
						} else if (space->kind==3) {
							printLs(&space->m.ls);
						} else {
							printSpaceArray(space->m.sep);
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
		unsigned int i=0;
		unsigned int j=0;
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
			unsigned int i=0;
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
			unsigned int i=0;
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
		printTAB();printf("vars=\n");
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
		printTAB();printf("nDir=%d\n",(typ->nDir));
		printTAB();printf("isTwoDir=%d\n",(typ->isTwoDir));
		printTAB();printf("argkind=\n");
					printArgKind(typ->argkind);
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
			unsigned int i=0;
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


void printNormalArray(noll_uid_array* arr) {
		if (arr) {
			uid_t i=0;
			printTAB();printf("size=%d\n", arr->size_);tabn++;
			printTAB();printf("[");
			for(;i<arr->size_;i++) {
				printf("%d,\t", arr->data_[i]);
			}
			printf("]\n");tabn--;
		}
}

void printArgKind(noll_uid_array* arr) {
		if (arr) {
			uid_t i=0;
			printTAB();printf("size=%d\n", arr->size_);tabn++;
			printTAB();printf("[");
			for(;i<arr->size_;i++) {
				printf("%s,\t", getEnumAtype(arr->data_[i]));
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
			unsigned int i=0;
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
			unsigned int i=0;
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

