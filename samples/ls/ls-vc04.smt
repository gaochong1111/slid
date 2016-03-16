
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

;; declare set of locations

(declare-fun alpha0 () SetLoc)

(assert 
	(tobool 
		(pto x_emp (ref next y_emp) ) 
	)

)

(assert (not 
	(tobool 
		(index alpha0 (ls x_emp y_emp )) 
	)

))

(check-sat)
