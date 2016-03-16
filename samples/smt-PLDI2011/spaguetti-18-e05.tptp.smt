
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
(declare-fun x21 () Sll_t)
(declare-fun x22 () Sll_t)

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
	(and (= nil nil) (distinct x6 x7) (distinct x6 x9) (distinct x11 x15) (distinct x11 x14) (distinct x3 x4) (distinct x7 x18) (distinct x7 x17) (distinct x7 x14) (distinct x9 x15) (distinct x2 x8) (distinct x2 x6) (distinct x2 x11) (distinct x2 x17) (distinct x14 x15) (distinct x8 x13) (distinct x8 x15) (distinct x1 x8) (distinct x1 x11) (distinct x1 x7) (distinct x1 x10) (distinct x1 x14) (distinct x1 x15) (distinct x1 x5) (distinct x4 x6) (distinct x4 x9) (distinct x4 x12) (distinct x4 x5) (distinct x10 x13) (distinct x10 x17) (distinct x10 x14) (distinct x13 x18) (distinct x13 x16) (distinct x5 x11) (distinct x5 x10) (distinct x5 x12) 
	(tobool 
	(ssep 
		(index alpha0 (ls x5 x6 )) 
		(index alpha1 (ls x16 x9 )) 
		(index alpha2 (ls x4 x13 )) 
		(index alpha3 (ls x8 x16 )) 
		(index alpha4 (ls x14 x9 )) 
		(index alpha5 (ls x14 x16 )) 
		(index alpha6 (ls x12 x15 )) 
		(index alpha7 (ls x12 x7 )) 
		(index alpha8 (ls x12 x3 )) 
		(index alpha9 (ls x2 x7 )) 
		(index alpha10 (ls x9 x12 )) 
		(index alpha11 (ls x11 x7 )) 
	)

	)

	)

)

(check-sat)
