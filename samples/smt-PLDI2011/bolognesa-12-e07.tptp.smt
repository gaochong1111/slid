
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
		(pto x7 (ref next x10) ) 
		(pto x4 (ref next x11) ) 
		(pto x6 (ref next x5) ) 
		(index alpha0 (ls x9 x5 )) 
		(pto x10 (ref next x12) ) 
		(index alpha1 (ls x3 x8 )) 
		(pto x1 (ref next x2) ) 
		(pto x11 (ref next x1) ) 
		(pto x5 (ref next x4) ) 
		(pto x12 (ref next x9) ) 
		(index alpha2 (ls x2 x8 )) 
		(index alpha3 (ls x8 x11 )) 
	)

	)

	)

)

(assert (not 
	(tobool 
	(ssep 
		(index alpha4 (ls x7 x12 )) 
		(index alpha5 (ls x12 x5 )) 
		(index alpha6 (ls x3 x8 )) 
		(index alpha7 (ls x8 x11 )) 
		(index alpha8 (ls x6 x11 )) 
		(index alpha9 (ls x11 x8 )) 
	)

	)

))

(check-sat)
