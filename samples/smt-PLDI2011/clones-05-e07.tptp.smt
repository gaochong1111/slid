
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

(assert 
	(and (= nil nil) (distinct nil x1) (distinct nil x2) (distinct nil x4) (distinct nil x5) (distinct nil x7) (distinct nil x8) (distinct nil x10) (distinct nil x11) (distinct nil x13) (distinct nil x14) 
	(tobool 
	(ssep 
		(index alpha0 (ls x13 x14 )) 
		(pto x14 (ref next x13) ) 
		(index alpha1 (ls x10 x11 )) 
		(pto x11 (ref next x10) ) 
		(index alpha2 (ls x7 x8 )) 
		(pto x8 (ref next x7) ) 
		(index alpha3 (ls x4 x5 )) 
		(pto x5 (ref next x4) ) 
		(index alpha4 (ls x1 x2 )) 
		(pto x2 (ref next x1) ) 
	)

	)

	)

)

(assert (not 
	(tobool 
	(ssep 
		(index alpha5 (ls x15 x14 )) 
		(pto x14 (ref next x15) ) 
		(index alpha6 (ls x12 x11 )) 
		(pto x11 (ref next x12) ) 
		(index alpha7 (ls x9 x8 )) 
		(pto x8 (ref next x9) ) 
		(index alpha8 (ls x6 x5 )) 
		(pto x5 (ref next x6) ) 
		(index alpha9 (ls x3 x2 )) 
		(pto x2 (ref next x3) ) 
	)

	)

))

(check-sat)
