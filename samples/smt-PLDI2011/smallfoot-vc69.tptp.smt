
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
(declare-fun x0 () Sll_t)
(declare-fun x1 () Sll_t)
(declare-fun x2 () Sll_t)
(declare-fun x3 () Sll_t)
(declare-fun x4 () Sll_t)
(declare-fun x5 () Sll_t)
(declare-fun x6 () Sll_t)
(declare-fun x7 () Sll_t)

;; declare set of locations

(declare-fun alpha0 () SetLoc)

(assert 
	(and (= nil nil) (distinct nil x1) (distinct x1 x2) (distinct x1 x3) 
	(tobool 
	(ssep 
		(pto x1 (ref next x3) ) 
		(index alpha0 (ls x2 nil )) 
	)

	)

	)

)

(assert (not 
	(and (= x2 x2) 
	(tobool emp)

	)

))

(check-sat)
