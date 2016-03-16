
(set-logic QF_S)

;; declare sorts
(declare-sort Dll_t 0)


;; declare fields
(declare-fun next () (Field Dll_t Dll_t))
(declare-fun prev () (Field Dll_t Dll_t))


;; declare predicates

(define-fun dll ((?fr Dll_t) (?bk Dll_t) (?pr Dll_t) (?nx Dll_t) ) Space (tospace 
	(or 
	(and (= ?fr ?nx) (= ?bk ?pr) 
		(tobool emp
		)

	)
 
	(exists ((?u Dll_t) ) 
	(and (distinct ?fr ?nx) (distinct ?bk ?pr) 
		(tobool (ssep 
		(pto ?fr (sref (ref next ?u) (ref prev ?pr) ) ) 
		(dll ?u ?bk ?fr ?nx )
		) )

	)
 
	)

	)
))

;; declare variables
(declare-fun x () Dll_t)
(declare-fun y () Dll_t)
(declare-fun z () Dll_t)
(declare-fun x1 () Dll_t)
(declare-fun x2 () Dll_t)
(declare-fun x3 () Dll_t)
(declare-fun x4 () Dll_t)

;; declare set of locations

(declare-fun alpha0 () SetLoc)

(assert 
	(and (distinct x z) (distinct z x1) (distinct z x2) (distinct z x3) (distinct z x4) (distinct y z) 
	(tobool 
	(ssep 
		(pto x (sref (ref next x1) (ref prev nil) ) ) 
		(pto x1 (sref (ref next x2) (ref prev x) ) ) 
		(pto x2 (sref (ref next x3) (ref prev x1) ) ) 
		(pto x3 (sref (ref next x4) (ref prev x2) ) ) 
		(pto x4 (sref (ref next y) (ref prev x3) ) ) 
		(pto y (sref (ref next z) (ref prev x4) ) ) 
	)

	)

	)

)

(assert (not 
	(tobool 
		(index alpha0 (dll x y nil z )) 
	)

))

(check-sat)
