
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
(declare-fun x8 () Sll_t)

;; declare set of locations

(declare-fun alpha0 () SetLoc)
(declare-fun alpha1 () SetLoc)

(assert 
	(and (= nil nil) (distinct nil x1) (distinct nil x2) (distinct nil x3) (distinct x1 x2) (distinct x1 x3) 
	(tobool 
	(ssep 
		(index alpha0 (ls x2 x3 )) 
		(pto x1 (ref next x2) ) 
		(pto x3 (ref next x1) ) 
	)

	)

	)

)

(assert (not 
	(and (distinct x3 x4) 
	(tobool 
	(ssep 
		(index alpha1 (ls x4 x3 )) 
		(pto x3 (ref next x4) ) 
	)

	)

	)

))

(check-sat)
