
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

(assert 
	(and (= nil nil) 
	(tobool 
	(ssep 
		(index alpha0 (ls x11 x8 )) 
		(pto x10 (ref next x12) ) 
		(pto x7 (ref next x14) ) 
		(pto x3 (ref next x12) ) 
		(pto x5 (ref next x9) ) 
		(pto x8 (ref next x12) ) 
		(pto x13 (ref next x11) ) 
		(pto x12 (ref next x9) ) 
		(pto x14 (ref next x5) ) 
		(pto x6 (ref next x3) ) 
		(pto x4 (ref next x11) ) 
		(index alpha1 (ls x1 x7 )) 
		(pto x2 (ref next x1) ) 
		(pto x9 (ref next x13) ) 
	)

	)

	)

)

(assert (not 
	(tobool 
	(ssep 
		(index alpha2 (ls x4 x11 )) 
		(index alpha3 (ls x2 x7 )) 
		(index alpha4 (ls x8 x12 )) 
		(index alpha5 (ls x10 x12 )) 
		(index alpha6 (ls x6 x12 )) 
		(index alpha7 (ls x7 x5 )) 
		(index alpha8 (ls x5 x9 )) 
		(index alpha9 (ls x12 x8 )) 
	)

	)

))

(check-sat)
