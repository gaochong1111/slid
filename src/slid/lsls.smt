
(set-logic QF_SLRDI)

;; declare sorts
(declare-sort Sll_t 0)


;; declare fields
(declare-fun next () (Field Sll_t Sll_t))
(declare-fun data () (Field Sll_t Int))

;; declare predicates

(
define-fun lsls 
	((?in Sll_t) (?dt1 Int) (?len1 Int) (?out Sll_t) (?dt2 Int) (?len2 Int)) 
	Space 
	(tospace 
		(or 
			(and (= ?in ?out) (= ?dt1 ?dt2) (= ?len1 ?len2) 
			(tobool emp)
			)

 
			(exists 
				((?u Sll_t) (?dt3 Int) (?len3 Int)) 
				(and  	
					(<= ?dt1 ?dt3)
					(= ?len1 (+ ?len3 1))
					(tobool (ssep 
						(pto ?in (sref (ref next ?u) (ref data ?dt3)) ) 
						(lsls ?u ?dt3 ?len3 ?out ?dt2 ?len2)
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
(declare-fun d1 () Int)
(declare-fun d2 () Int)
(declare-fun n1 () Int)
(declare-fun n2 () Int)


;; declare set of locations

(declare-fun alpha0 () SetLoc)

(assert 
	(and
	(distinct d1 d2)
	(tobool 
 	        (ssep 
                (pto y_emp (sref (ref next z_emp) (ref data d1)) )
		(index alpha0 (lsls y_emp d1 n1 w_emp d2 n2)) 
		)
	)
	)
)

(check-sat)
