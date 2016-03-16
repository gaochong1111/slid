
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
(declare-fun y_emp () Dll_t)
(declare-fun w_emp () Dll_t)
(declare-fun u_emp () Dll_t)
(declare-fun t_emp () Dll_t)

;; declare set of locations

(declare-fun alpha0 () SetLoc)
(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)

(assert 
	(and (distinct x_emp w_emp) (distinct w_emp t_emp) (distinct nil w_emp) 
	(tobool 
	(ssep 
		(pto w_emp (sref (ref next t_emp) (ref prev u_emp) ) ) 
		(index alpha0 (dll x_emp u_emp nil w_emp )) 
		(index alpha1 (dll t_emp y_emp w_emp nil )) 
	)

	)

	)

)

(assert (not 
	(tobool 
		(index alpha2 (dll x_emp y_emp nil nil )) 
	)

))

(check-sat)
