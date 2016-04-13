
(set-logic QF_SLRDI)

(declare-sort Lseg_t 0)

(declare-fun next() (Field Lseg_t Lseg_t))

(define-fun lseg
	((?E Lseg_t) (?F Lseg_t)) Space 
		(tospace
			(or
				(and
					(= ?E ?F)
					(tobool 
						emp
					)
				)
				(exists
					((?X Lseg_t) )
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


(declare-fun Y() Lseg_t)
(declare-fun Z() Lseg_t)
(declare-fun W() Lseg_t)

(declare-fun alpha0() SetLoc)

(assert
	(tobool
		(ssep
			(pto Y (ref next Z))
			(index alpha0 (lseg Y W))
		)
	)
)

(check-sat)
