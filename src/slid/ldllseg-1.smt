(set-logic QF_SLRDI)

(declare-sort Ldll_t 0)

(declare-fun next() (Field Ldll_t Ldll_t))
(declare-fun prev() (Field Ldll_t Ldll_t))

(define-fun ldllseg
	((?E Ldll_t) (?P Ldll_t) (?x0 Int) (?F Ldll_t) (?L Ldll_t) (?x1 Int) (?n Int)) Space
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
					(>= ?x0 (+ ?x2 2))
					(>= ?x0 (+ ?n 4))
					(>= ?x0 8)
					(<= ?x0 (+ ?x2 -3))
					(<= ?x0 (+ ?n 6))
					(<= ?x0 9)
					(tobool
						(ssep
							(pto ?E (sref (ref next ?X) (ref prev ?P) ))
							(ldllseg ?X ?E ?x2 ?F ?L ?x1 ?n)
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
(declare-fun x1() Int)
(declare-fun x2() Int)
(declare-fun n() Int)

(declare-fun alpha0() SetLoc)

(assert
	(and
		(distinct E1 E4)
		(distinct E2 E3)
		(tobool
			(ssep
				(pto E1 (sref (ref next E3) (ref prev E2)))
				(index alpha0 (ldllseg E1 E3 x1 E2 E4 x2 n))
			)
		)
	)
)

(check-sat)
