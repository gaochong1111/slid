
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
(declare-fun x25 () Sll_t)
(declare-fun x26 () Sll_t)
(declare-fun x27 () Sll_t)
(declare-fun x28 () Sll_t)

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
	(and (= nil nil) (distinct nil x1) (distinct nil x2) (distinct nil x3) (distinct x1 x3) (distinct x2 x3) (distinct nil x5) (distinct nil x6) (distinct nil x7) (distinct x5 x7) (distinct x6 x7) (distinct nil x9) (distinct nil x10) (distinct nil x11) (distinct x9 x11) (distinct x10 x11) (distinct nil x13) (distinct nil x14) (distinct nil x15) (distinct x13 x15) (distinct x14 x15) (distinct nil x17) (distinct nil x18) (distinct nil x19) (distinct x17 x19) (distinct x18 x19) (distinct nil x21) (distinct nil x22) (distinct nil x23) (distinct x21 x23) (distinct x22 x23) 
	(tobool 
	(ssep 
		(index alpha0 (ls x22 x21 )) 
		(pto x23 (ref next x22) ) 
		(pto x21 (ref next x23) ) 
		(index alpha1 (ls x18 x17 )) 
		(pto x19 (ref next x18) ) 
		(pto x17 (ref next x19) ) 
		(index alpha2 (ls x14 x13 )) 
		(pto x15 (ref next x14) ) 
		(pto x13 (ref next x15) ) 
		(index alpha3 (ls x10 x9 )) 
		(pto x11 (ref next x10) ) 
		(pto x9 (ref next x11) ) 
		(index alpha4 (ls x6 x5 )) 
		(pto x7 (ref next x6) ) 
		(pto x5 (ref next x7) ) 
		(index alpha5 (ls x2 x1 )) 
		(pto x3 (ref next x2) ) 
		(pto x1 (ref next x3) ) 
	)

	)

	)

)

(assert (not 
	(tobool 
	(ssep 
		(pto x24 (ref next x23) ) 
		(index alpha6 (ls x22 x24 )) 
		(pto x23 (ref next x22) ) 
		(pto x20 (ref next x19) ) 
		(index alpha7 (ls x18 x20 )) 
		(pto x19 (ref next x18) ) 
		(pto x16 (ref next x15) ) 
		(index alpha8 (ls x14 x16 )) 
		(pto x15 (ref next x14) ) 
		(pto x12 (ref next x11) ) 
		(index alpha9 (ls x10 x12 )) 
		(pto x11 (ref next x10) ) 
		(pto x8 (ref next x7) ) 
		(index alpha10 (ls x6 x8 )) 
		(pto x7 (ref next x6) ) 
		(pto x4 (ref next x3) ) 
		(index alpha11 (ls x2 x4 )) 
		(pto x3 (ref next x2) ) 
	)

	)

))

(check-sat)
