
(set-logic QF_SLRDI)

;; declare sorts
(declare-sort Sll_t 0)


;; declare fields
(declare-fun next () (Field Sll_t Sll_t))


;; declare predicates

(
define-fun lls 
	((?in Sll_t)  (?out Sll_t) (?len1 Int) (?len2 Int)) 
	Space 
	(tospace 
		(or 
			(and
				 (= ?in ?out) 
				 (= ?len1 ?len2) 
				(tobool emp)
			)

 
			(exists 
				((?u Sll_t) (?len3 Int)) 
				(and  
					(= ?len1 (+ ?len3 1))
					(tobool (ssep 
						(pto ?in (ref next ?u) ) 
						(lls ?u ?out  ?len3 ?len2)
						) 
					)

				)
 

			)
		)
	)
)

;; declare variables
(declare-fun y_emp () Sll_t)
(declare-fun w_emp () Sll_t)
(declare-fun z_emp () Sll_t)
(declare-fun n1 () Int)
(declare-fun n2 () Int)


;; declare set of locations

(declare-fun alpha0 () SetLoc)

(assert 
	(and
	(> n1 n2)
	(tobool 
 	        (ssep 
                (pto y_emp (ref next z_emp))
		(index alpha0 (lls y_emp  w_emp n1 n2)) 
		)
	)
	)
)

(check-sat)
