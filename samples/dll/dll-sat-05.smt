(set-logic QF_SLRDI)

(declare-sort Ldll_t 0)

(declare-fun next() (Field Ldll_t Ldll_t))
(declare-fun prev() (Field Ldll_t Ldll_t))
(declare-fun data() (Field Ldll_t Int))


(define-fun dll
	((?E Ldll_t) (?P Ldll_t) (?x1 Int) (?len1 Int) (?F Ldll_t) (?L Ldll_t) (?x2 Int) (?len2 Int)) Space
	(tospace
		 (or
			(and
				(= ?E ?F)
				(= ?P ?L)
				(= ?x1 ?x2)
				(= ?len1 ?len2) 
				(tobool emp)
			)
			(exists
				((?X Ldll_t) (?x3 Int)(?len3 Int))
				(and					
					(<= ?x1 ?x3)
					(= ?len1 (+ ?len3 1))
					(tobool
						(ssep
							(pto ?E (sref (ref next ?X) (ref prev ?P) (ref data ?x1)))
							(dll ?X ?E ?x3 ?len3 ?F ?L ?x2 ?len2)
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
(declare-fun len1() Int)
(declare-fun len2() Int)
;(declare-fun n() Int)

(declare-fun alpha0() SetLoc)

(assert
	(and
		(= E1 E4)
		(= len1 (+ len2 1))
		(tobool
			(ssep
				(pto E3 (sref (ref next E4) (ref prev E2)))
				(index alpha0 (dll E1 E3 x1 len1 E2 E4 x2 len2))
			)
		)
	)
)

(check-sat)

