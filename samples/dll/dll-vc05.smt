
(set-logic QF_S)

;; declare sorts
(declare-sort Dll_t 0)


;; declare fields
(declare-fun next () (Field Dll_t Dll_t))
(declare-fun prev () (Field Dll_t Dll_t))


;; declare predicates

(define-fun dll ((?fr Dll_t) (?bk Dll_t) (?pr Dll_t) (?nx Dll_t) ) Space (tospace 
	(or 
	(and (= ?fr ?nx) (= ?bk ?pr) 
		(tobool emp
		)

	)
 
	(exists ((?u Dll_t) ) 
	(and (distinct ?fr ?nx) (distinct ?bk ?pr) 
		(tobool (ssep 
		(pto ?fr (sref (ref next ?u) (ref prev ?pr) ) ) 
		(dll ?u ?bk ?fr ?nx )
		) )

	)
 
	)

	)
))

;; declare variables
(declare-fun x_emp () Dll_t)
(declare-fun w_emp () Dll_t)
(declare-fun y_emp () Dll_t)
(declare-fun z_emp () Dll_t)

;; declare set of locations

(declare-fun alpha0 () SetLoc)
(declare-fun alpha1 () SetLoc)

(assert 
	(tobool 
	(ssep 
		(pto x_emp (sref (ref next w_emp) (ref prev nil) ) ) 
		(index alpha0 (dll w_emp y_emp x_emp z_emp )) 
		(pto y_emp (ref next z_emp) ) 
	)

	)

)

(assert (not 
	(tobool 
		(index alpha1 (dll x_emp y_emp nil z_emp )) 
	)

))

(check-sat)
