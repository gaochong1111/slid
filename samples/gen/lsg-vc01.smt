
(set-logic QF_S)

;; declare sorts
(declare-sort Sll_t 0)


;; declare fields
(declare-fun next () (Field Sll_t Sll_t))


;; declare predicates

(define-fun lsg ((?in Sll_t) (?out Sll_t) ) Space (tospace 
	(or 
	(and (= ?in ?out) 
		(tobool emp
		)

	)
 
	(exists ((?u Sll_t) ) 
	(and (distinct ?in ?out) 
		(tobool (ssep 
		(pto ?in (ref next ?u) ) 
		(lsg ?u ?out )
		) )

	)
 
	)

	)
))

;; declare variables
(declare-fun x_emp () Sll_t)
(declare-fun y_emp () Sll_t)
(declare-fun z_emp () Sll_t)

;; declare set of locations

(declare-fun alpha0 () SetLoc)

(assert 
	(tobool 
	(ssep 
		(pto x_emp (ref next y_emp) ) 
		(pto y_emp (ref next z_emp) ) 
	)

	)

)

(assert (not 
	(tobool 
		(index alpha0 (lsg x_emp z_emp )) 
	)

))

(check-sat)
