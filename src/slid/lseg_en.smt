(set-logic QF_SLRDI)

(declare-sort sls_t 0)
;(declare-sort Lseg_t 0)


(declare-fun next () (Field sls_t Int))

(
define-fun slseg ((?E sls_t) (?d1 Int) (?F sls_t) (?d2 Int)) Space
	(tospace 
		(or
			(and (= ?E ?F) (= ?d1 ?d2)
			(tobool emp)
			)

			(exists ((?X sls_t) (?d3 Int))
				(and
					(<= ?d1 ?d3)
					(tobool (ssep
							(pto ?E (ref next ?X))
							(slseg ?X ?d3 ?F ?d2)
					    	)
					)
				)
			)
		)
	)
)
(define-fun lseg
	((?E sls_t) (?F sls_t)) Space 
		(tospace
			(or
				(and
					(= ?E ?F)
					(tobool 
						emp
					)
				)
				(exists
					((?X sls_t) )
					(and
						(tobool
							(ssep
								(pto ?E (ref next ?X))
								(lseg ?X ?F)
							)
						)
					)
				)
			)
		)
	
)

(declare-fun x () sls_t)
(declare-fun y () sls_t)
;(declare-fun z () sls_t)
(declare-fun a () Int)
(declare-fun b () Int)

(declare-fun alpha0 () SetLoc)

(assert
	(and
		;(< a b)
		(tobool
			;(ssep
				;(pto x (ref next z))
				(index alpha0 (slseg x a y b))
			;)
		)
	)
)

(assert
	(not
	(and
		;(< a b)
		(tobool
			;(ssep
				;(pto x (ref next z))
				(index alpha0 (lseg x y))
			;)
		)
	)
)
)

(check-sat)
