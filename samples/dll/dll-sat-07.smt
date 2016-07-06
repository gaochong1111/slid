(set-logic QF_SLRDI)

(declare-sort Ldll_t 0)

(declare-fun next() (Field Ldll_t Ldll_t))
(declare-fun prev() (Field Ldll_t Ldll_t))
(declare-fun data() (Field Ldll_t Int))

(define-fun ldllseg
	((?E Ldll_t) (?P Ldll_t) (?x0 Int)(?l0 Int) (?F Ldll_t) (?L Ldll_t) (?x1 Int)(?l1 Int) (?n Int)) 
	Space
	(tospace
		 (or
			(and
				(= ?E ?F)
				(= ?P ?L)
				(= ?x0 ?x1) 
				(= ?l0 ?l1)
			)
			(exists
				((?X Ldll_t) (?x2 Int)(?l2 Int))
				(and
					(<= ?x0 ?n)
					(<= ?x0 (+ ?x2 -2))
					(= ?l0 (+ ?l2 1))
					(tobool
						(ssep
							(pto ?E (sref (ref next ?X) (ref prev ?P) (ref data ?x0) ))
							(ldllseg ?X ?E ?x2 ?l2 ?F ?L ?x1 ?l1 ?n)
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
(declare-fun x0() Int)
(declare-fun x1() Int)
(declare-fun x2() Int)
(declare-fun l1() Int)
(declare-fun l2() Int)
(declare-fun n() Int)

(declare-fun alpha0() SetLoc)

(assert
	(and
		(distinct x1 x2)
		(tobool
			(ssep
				(pto E1 (sref (ref next E3) (ref prev E2) (ref data x0)))
				(index alpha0 (ldllseg E1 E3 x1 l1 E2 E4 x2 l2 n))
			)
		)
	)
)

(check-sat)
