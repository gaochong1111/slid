
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
(declare-fun alpha12 () SetLoc)
(declare-fun alpha13 () SetLoc)
(declare-fun alpha14 () SetLoc)

(assert 
	(and (= nil nil) (distinct x11 x12) (distinct x11 x14) (distinct x7 x8) (distinct x7 x18) (distinct x2 x6) (distinct x2 x8) (distinct x2 x15) (distinct x1 x8) (distinct x1 x3) (distinct x1 x9) (distinct x1 x16) (distinct x13 x14) (distinct x16 x17) (distinct x6 x8) (distinct x6 x10) (distinct x3 x12) (distinct x9 x16) (distinct x9 x13) (distinct x9 x17) (distinct x12 x17) (distinct x15 x17) (distinct x14 x15) (distinct x8 x14) (distinct x4 x7) (distinct x4 x16) (distinct x10 x11) (distinct x5 x18) (distinct x5 x10) 
	(tobool 
	(ssep 
		(index alpha0 (ls x13 x7 )) 
		(index alpha1 (ls x13 x4 )) 
		(index alpha2 (ls x13 x6 )) 
		(index alpha3 (ls x10 x8 )) 
		(index alpha4 (ls x18 x14 )) 
		(index alpha5 (ls x18 x6 )) 
		(index alpha6 (ls x8 x5 )) 
		(index alpha7 (ls x17 x5 )) 
		(index alpha8 (ls x17 x16 )) 
		(index alpha9 (ls x2 x3 )) 
		(index alpha10 (ls x9 x17 )) 
		(index alpha11 (ls x7 x10 )) 
		(index alpha12 (ls x3 x13 )) 
		(index alpha13 (ls x3 x10 )) 
		(index alpha14 (ls x11 x15 )) 
	)

	)

	)

)

(check-sat)
