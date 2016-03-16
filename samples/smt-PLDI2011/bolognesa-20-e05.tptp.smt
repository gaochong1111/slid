
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
(declare-fun x23 () Sll_t)
(declare-fun x24 () Sll_t)

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
(declare-fun alpha15 () SetLoc)
(declare-fun alpha16 () SetLoc)
(declare-fun alpha17 () SetLoc)
(declare-fun alpha18 () SetLoc)
(declare-fun alpha19 () SetLoc)
(declare-fun alpha20 () SetLoc)

(assert 
	(and (= nil nil) 
	(tobool 
	(ssep 
		(index alpha0 (ls x18 x11 )) 
		(index alpha1 (ls x2 x6 )) 
		(pto x1 (ref next x10) ) 
		(pto x14 (ref next x4) ) 
		(pto x15 (ref next x6) ) 
		(pto x16 (ref next x7) ) 
		(pto x11 (ref next x7) ) 
		(pto x9 (ref next x6) ) 
		(index alpha2 (ls x7 x4 )) 
		(pto x4 (ref next x7) ) 
		(index alpha3 (ls x13 x1 )) 
		(index alpha4 (ls x20 x12 )) 
		(pto x3 (ref next x10) ) 
		(index alpha5 (ls x6 x3 )) 
		(index alpha6 (ls x19 x18 )) 
		(pto x10 (ref next x6) ) 
		(index alpha7 (ls x8 x14 )) 
		(pto x12 (ref next x5) ) 
		(pto x17 (ref next x20) ) 
		(pto x5 (ref next x11) ) 
	)

	)

	)

)

(assert (not 
	(tobool 
	(ssep 
		(index alpha8 (ls x2 x6 )) 
		(index alpha9 (ls x16 x7 )) 
		(index alpha10 (ls x17 x20 )) 
		(index alpha11 (ls x20 x12 )) 
		(index alpha12 (ls x15 x6 )) 
		(index alpha13 (ls x9 x3 )) 
		(index alpha14 (ls x8 x4 )) 
		(index alpha15 (ls x12 x11 )) 
		(index alpha16 (ls x4 x7 )) 
		(index alpha17 (ls x19 x11 )) 
		(index alpha18 (ls x13 x10 )) 
		(index alpha19 (ls x3 x6 )) 
		(index alpha20 (ls x11 x4 )) 
	)

	)

))

(check-sat)
