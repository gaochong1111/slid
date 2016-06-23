(set-logic QF_SLRDI)

(declare-sort Ldll_t 0)

(declare-fun next() (Field Ldll_t Ldll_t))
(declare-fun prev() (Field Ldll_t Ldll_t))

(define-fun ldllseg
	((?E Ldll_t) (?P Ldll_t) (?x0 Int) (?F Ldll_t) (?L Ldll_t) (?x1 Int)) Space
	(tospace
		 (or
			(and
				(= ?E ?F)
				(= ?P ?L)
				(= ?x0 ?x1) 
			)
			(exists
				((?X Ldll_t) (?x2 Int))
				(and
					;(>= ?x0 5)
					(= ?x0 (+ ?x2 1))
					(tobool
						(ssep
							(pto ?E (sref (ref next ?X) (ref prev ?P) ))
							(ldllseg ?X ?E ?x2 ?F ?L ?x1)
						)
					)
				)
			)
		)
	)
)
(define-fun dllseg
	((?E Ldll_t) (?F Ldll_t)) Space
	(tospace
		 (or
			(and
				(= ?E ?F)
			)
			(exists
				((?X Ldll_t) (?Y Ldll_t))
				(and
					;(>= ?x0 5)
					;(= ?x0 (+ ?x2 1))
					(tobool
						(ssep
							(pto ?E (sref (ref next ?X) (ref prev ?Y) ))
							(dllseg ?X ?F)
						)
					)
				)
			)
		)
	)
)

(declare-fun E1() Ldll_t)
(declare-fun E2() Ldll_t)
(declare-fun E3() Ldll_t)
(declare-fun E4() Ldll_t)
(declare-fun n1() Int)
(declare-fun n2() Int)

(declare-fun alpha0() SetLoc)

(assert
	(and
		(<= n1 (+ n2 6))
		(>= n1 (+ n2 5))
		(tobool
			(index alpha0 (ldllseg E1 E3 n1 E2 E4 n2))
		)
	)
)

(assert
	(not
		(and
			(distinct E1 E4)
			(tobool
				(index alpha0 (dllseg E1 E2))
			)
		)
	)
)

(check-sat)
