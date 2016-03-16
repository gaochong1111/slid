
(set-logic QF_S)

;; declare sorts
(declare-sort NLL_lvl1_t 0)
(declare-sort NLL_lvl2_t 0)
(declare-sort NLL_lvl3_t 0)


;; declare fields
(declare-fun next1 () (Field NLL_lvl1_t NLL_lvl1_t))
(declare-fun next2 () (Field NLL_lvl2_t NLL_lvl2_t))
(declare-fun next3 () (Field NLL_lvl3_t NLL_lvl3_t))
(declare-fun down2 () (Field NLL_lvl2_t NLL_lvl1_t))
(declare-fun down3 () (Field NLL_lvl3_t NLL_lvl2_t))


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


(define-fun nllg ((?in NLL_lvl2_t) (?out NLL_lvl2_t) (?boundary NLL_lvl1_t) ) Space (tospace 
	(or 
	(and (= ?in ?out) 
		(tobool emp
		)

	)
 
	(exists ((?u NLL_lvl2_t) (?Z1 NLL_lvl1_t) ) 
	(and (distinct ?in ?out) 
		(tobool (ssep 
		(pto ?in (sref (ref next2 ?u) (ref down2 ?Z1) ) ) 
		(lso ?Z1 ?boundary )
		(nllg ?u ?out ?boundary )
		) )

	)
 
	)

	)
))


(define-fun nnllg ((?in NLL_lvl3_t) (?out NLL_lvl3_t) (?b2 NLL_lvl2_t) (?b1 NLL_lvl1_t) ) Space (tospace 
	(or 
	(and (= ?in ?out) 
		(tobool emp
		)

	)
 
	(exists ((?u NLL_lvl3_t) (?Z2 NLL_lvl2_t) ) 
	(and (distinct ?in ?out) 
		(tobool (ssep 
		(pto ?in (sref (ref next3 ?u) (ref down3 ?Z2) ) ) 
		(nllg ?Z2 ?b2 ?b1 )
		(nnllg ?u ?out ?b2 ?b1 )
		) )

	)
 
	)

	)
))

;; declare variables
(declare-fun x3 () NLL_lvl3_t)
(declare-fun x2 () NLL_lvl2_t)
(declare-fun x1 () NLL_lvl1_t)

;; declare set of locations

(declare-fun alpha0 () SetLoc)

(assert 
	(tobool 
	(ssep 
		(pto x3 (sref (ref next3 nil) (ref down3 x2) ) ) 
		(pto x2 (sref (ref next2 nil) (ref down2 x1) ) ) 
		(pto x1 (ref next1 nil) )
)))

 

(assert (not 
	(tobool 
		(index alpha0 (nnllg x3 nil nil nil )) 
	)

))

(check-sat)
