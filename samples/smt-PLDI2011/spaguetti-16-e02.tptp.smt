
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
(declare-fun x20 () Sll_t)

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
(declare-fun alpha11 () SetLoc)

(assert 
	(and (= nil nil) (distinct x6 x11) (distinct x6 x7) (distinct x3 x10) (distinct x3 x14) (distinct x7 x15) (distinct x9 x15) (distinct x9 x14) (distinct x2 x16) (distinct x2 x5) (distinct x14 x16) (distinct x10 x11) (distinct x13 x15) (distinct x5 x9) (distinct x5 x16) (distinct x5 x15) 
	(tobool 
	(ssep 
		(index alpha0 (ls x14 x12 )) 
		(index alpha1 (ls x2 x13 )) 
		(index alpha2 (ls x13 x6 )) 
		(index alpha3 (ls x13 x8 )) 
		(index alpha4 (ls x10 x2 )) 
		(index alpha5 (ls x10 x3 )) 
		(index alpha6 (ls x7 x2 )) 
		(index alpha7 (ls x7 x16 )) 
		(index alpha8 (ls x3 x14 )) 
		(index alpha9 (ls x11 x4 )) 
		(index alpha10 (ls x6 x14 )) 
		(index alpha11 (ls x6 x16 )) 
	)

	)

	)

)

(check-sat)
