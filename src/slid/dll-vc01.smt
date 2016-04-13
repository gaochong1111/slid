
(set-logic QF_SLRDI)

;; declare sorts
(declare-sort Dll_t 0)


;; declare fields
(declare-fun next () (Field Dll_t Dll_t))
(declare-fun prev () (Field Dll_t Dll_t))


;; declare predicates

(define-fun dll ((?E Dll_t) (?P Dll_t) (?len1 Int) (?F Dll_t) (?L Dll_t) (?len2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F) (= ?P ?L) (= ?len1 ?len2)
		(tobool emp
		)

	)
 
	(exists ((?u Dll_t) (?len3 Int)) 
	(and (= ?len1 (+ ?len3 1)) 
		(tobool (ssep 
		(pto ?E (sref (ref next ?u) (ref prev ?P) ) ) 
		(dll ?u ?E ?len3 ?F ?L ?len2)
		) )

	)
 
	)

	)
))

;; declare variables
(declare-fun x1 () Dll_t)
(declare-fun x2 () Dll_t)
(declare-fun y1 () Dll_t)
(declare-fun y2 () Dll_t)
(declare-fun z () Dll_t)

(declare-fun n1 () Int)
(declare-fun n2 () Int)



;; declare set of locations

(declare-fun alpha0 () SetLoc)

(assert
	(and
		(> n1 n2)
		(tobool
			(ssep
				(pto y2 (ref next z))
				(index alpha0 (dll x1 x2 n1 y1 y2 n2))
			)
		)
	)
)

(check-sat)
