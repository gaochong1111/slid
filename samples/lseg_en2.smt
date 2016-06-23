(set-logic QF_SLRDI)

(declare-sort sls_t 0)
;(declare-sort Lseg_t 0)


(declare-fun next () (Field sls_t sls_t))
(declare-fun data () (Field sls_t Int))

(
define-fun slseg ((?E sls_t) (?d1 Int) (?d3 Int) (?F sls_t) (?d2 Int) (?d4 Int)) Space
	(tospace 
		(or
			(and (= ?E ?F) (= ?d1 ?d2) (= ?d3 ?d4)
			(tobool emp)
			)

			(exists ((?X sls_t) (?d5 Int) (?d6 Int))
				(and
					(= ?d1 (+ ?d5 1))
					(= ?d3 (+ ?d6 1))
					(tobool (ssep
							(pto ?E (sref (ref next ?X) (ref data ?d5) (ref data ?d6)))
							(slseg ?X ?d5 ?d6 ?F ?d2 ?d4)
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
					((?X sls_t) (?d5 Int))
					(and
						(tobool
							(ssep
								(pto ?E (sref (ref next ?X) (ref data ?d5) (ref data ?d5)))
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
				(index alpha0 (slseg x a a y b b))
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
