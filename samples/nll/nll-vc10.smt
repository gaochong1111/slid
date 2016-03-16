
(set-logic QF_S)

;; declare sorts
(declare-sort NLL_lvl1_t 0)
(declare-sort NLL_lvl2_t 0)


;; declare fields
(declare-fun next1 () (Field NLL_lvl1_t NLL_lvl1_t))
(declare-fun next2 () (Field NLL_lvl2_t NLL_lvl2_t))
(declare-fun down () (Field NLL_lvl2_t NLL_lvl1_t))


;; declare predicates

(define-fun lso ((?in NLL_lvl1_t) (?out NLL_lvl1_t) ) Space (tospace 
	(or 
	(and (= ?in ?out) 
		(tobool emp
		)

	)
 
	(exists ((?u NLL_lvl1_t) ) 
	(and (distinct ?in ?out) 
		(tobool (ssep 
		(pto ?in (ref next1 ?u) ) 
		(lso ?u ?out )
		) )

	)
 
	)

	)
))

(define-fun nll ((?in NLL_lvl2_t) (?out NLL_lvl2_t) (?boundary NLL_lvl1_t) ) Space (tospace 
	(or 
	(and (= ?in ?out) 
		(tobool emp
		)

	)
 
	(exists ((?u NLL_lvl2_t) (?Z1 NLL_lvl1_t) ) 
	(and (distinct ?in ?out) 
		(tobool (ssep 
		(pto ?in (sref (ref next2 ?u) (ref down ?Z1) ) ) 
		(lso ?Z1 ?boundary )
		(nll ?u ?out ?boundary )
		) )

	)
 
	)

	)
))

;; declare variables
(declare-fun x1 () NLL_lvl2_t)
(declare-fun x2 () NLL_lvl2_t)
(declare-fun x2_1 () NLL_lvl1_t)
(declare-fun x2_2 () NLL_lvl1_t)
(declare-fun x3 () NLL_lvl2_t)

;; declare set of locations

(declare-fun alpha0 () SetLoc)
(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)

(assert 
	(tobool 
	(ssep 
		(index alpha0 (nll x1 x2 nil )) 
		(pto x2 (sref (ref next2 x3) (ref down x2_1) ) ) 
		(index alpha1 (lso x2_1 x2_2 )) 
		(pto x2_2 (ref next1 nil) ) 
		(index alpha2 (nll x3 nil nil )) 
	)

	)

)

(assert (not 
	(tobool 
		(index alpha3 (nll x1 nil nil )) 
	)

))

(check-sat)
