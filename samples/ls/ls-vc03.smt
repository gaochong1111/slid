
(set-logic QF_S)

;; declare sorts
(declare-sort Sll_t 0)


;; declare fields
(declare-fun next () (Field Sll_t Sll_t))


;; declare predicates

(define-fun ls ((?in Sll_t) (?out Sll_t) ) Space (tospace 
	(or 
	(and (= ?in ?out) 
		(tobool emp
		)

	)
 
	(exists ((?u Sll_t) ) 
	(and (distinct ?in ?out) 
		(tobool (ssep 
		(pto ?in (ref next ?u) ) 
		(ls ?u ?out )
		) )

	)
 
	)

	)
))

;; declare variables
(declare-fun x_emp () Sll_t)
(declare-fun y_emp () Sll_t)
(declare-fun w_emp () Sll_t)
(declare-fun z_emp () Sll_t)
(declare-fun u_emp () Sll_t)
(declare-fun v_emp () Sll_t)
(declare-fun r_emp () Sll_t)
(declare-fun s_emp () Sll_t)

;; declare set of locations

(declare-fun alpha0 () SetLoc)
(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)

(assert 
	(tobool 
	(ssep 
		(pto x_emp (ref next y_emp) ) 
		(index alpha0 (ls y_emp w_emp )) 
		(index alpha1 (ls w_emp z_emp )) 
		(pto z_emp (ref next u_emp) ) 
		(pto u_emp (ref next v_emp) ) 
		(index alpha2 (ls v_emp r_emp )) 
		(pto r_emp (ref next s_emp) ) 
	)

	)

)

(assert (not 
	(tobool 
		(index alpha3 (ls x_emp s_emp )) 
	)

))

(check-sat)
