
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
(declare-fun x9 () Sll_t)
(declare-fun x10 () Sll_t)
(declare-fun x11 () Sll_t)
(declare-fun x12 () Sll_t)
(declare-fun x13 () Sll_t)
(declare-fun x14 () Sll_t)
(declare-fun x15 () Sll_t)
(declare-fun x16 () Sll_t)
(declare-fun x17 () Sll_t)
(declare-fun x18 () Sll_t)
(declare-fun x19 () Sll_t)

;; declare set of locations

(declare-fun alpha0 () SetLoc)
(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)
(declare-fun alpha5 () SetLoc)
(declare-fun alpha6 () SetLoc)
(declare-fun alpha7 () SetLoc)
(declare-fun alpha8 () SetLoc)
(declare-fun alpha9 () SetLoc)
(declare-fun alpha10 () SetLoc)

(assert 
	(and (= nil nil) (distinct x6 x12) (distinct x3 x6) (distinct x3 x12) (distinct x9 x15) (distinct x12 x15) (distinct x8 x11) (distinct x1 x7) (distinct x1 x5) (distinct x4 x9) (distinct x10 x11) (distinct x10 x15) 
	(tobool 
	(ssep 
		(index alpha0 (ls x10 x1 )) 
		(index alpha1 (ls x10 x11 )) 
		(index alpha2 (ls x13 x2 )) 
		(index alpha3 (ls x1 x10 )) 
		(index alpha4 (ls x4 x1 )) 
		(index alpha5 (ls x15 x4 )) 
		(index alpha6 (ls x12 x5 )) 
		(index alpha7 (ls x12 x13 )) 
		(index alpha8 (ls x7 x4 )) 
		(index alpha9 (ls x6 x10 )) 
		(index alpha10 (ls x6 x1 )) 
	)

	)

	)

)

(check-sat)
