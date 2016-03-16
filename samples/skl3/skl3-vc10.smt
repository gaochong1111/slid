
(set-logic QF_S)

;; declare sorts
(declare-sort SL3_t 0)


;; declare fields
(declare-fun n1 () (Field SL3_t SL3_t))
(declare-fun n2 () (Field SL3_t SL3_t))
(declare-fun n3 () (Field SL3_t SL3_t))


;; declare predicates

(define-fun skl1 ((?hd SL3_t) (?ex SL3_t) ) Space (tospace 
	(or 
	(and (= ?hd ?ex) 
		(tobool emp
		)

	)
 
	(exists ((?tl SL3_t) ) 
	(and (distinct ?hd ?ex) 
		(tobool (ssep 
		(pto ?hd (sref (ref n3 nil) (ref n2 nil) (ref n1 ?tl) ) ) 
		(skl1 ?tl ?ex )
		) )

	)
 
	)

	)
))

(define-fun skl2 ((?hd SL3_t) (?ex SL3_t) ) Space (tospace 
	(or 
	(and (= ?hd ?ex) 
		(tobool emp
		)

	)
 
	(exists ((?tl SL3_t) (?Z1 SL3_t) ) 
	(and (distinct ?hd ?ex) 
		(tobool (ssep 
		(pto ?hd (sref (ref n3 nil) (ref n2 ?tl) (ref n1 ?Z1) ) ) 
		(skl1 ?Z1 ?tl )
		(skl2 ?tl ?ex )
		) )

	)
 
	)

	)
))

(define-fun skl3 ((?hd SL3_t) (?ex SL3_t) ) Space (tospace 
	(or 
	(and (= ?hd ?ex) 
		(tobool emp
		)

	)
 
	(exists ((?tl SL3_t) (?Z1 SL3_t) (?Z2 SL3_t) ) 
	(and (distinct ?hd ?ex) 
		(tobool (ssep 
		(pto ?hd (sref (ref n3 ?tl) (ref n2 ?Z2) (ref n1 ?Z1) ) ) 
		(skl1 ?Z1 ?Z2 )
		(skl2 ?Z2 ?tl )
		(skl3 ?tl ?ex )
		) )

	)
 
	)

	)
))

;; declare variables
(declare-fun x1 () SL3_t)
(declare-fun x2 () SL3_t)
(declare-fun x2_1 () SL3_t)
(declare-fun x2_1_1 () SL3_t)
(declare-fun x2_2 () SL3_t)
(declare-fun x2_2_1 () SL3_t)
(declare-fun x3 () SL3_t)

;; declare set of locations

(declare-fun alpha0 () SetLoc)
(declare-fun alpha1 () SetLoc)

(assert 
	(tobool 
	(ssep 
		(index alpha0 (skl3 x1 x2 )) 
		(pto x2 (sref (ref n3 nil) (ref n2 x2_2) (ref n1 x2_1) ) ) 
		(pto x2_2 (sref (ref n3 nil) (ref n2 nil) (ref n1 x2_2_1) ) ) 
		(pto x2_1 (sref (ref n3 nil) (ref n2 nil) (ref n1 x2_1_1) ) ) 
		(pto x2_1_1 (sref (ref n3 nil) (ref n2 nil) (ref n1 x2_2) ) ) 
		(pto x2_2_1 (sref (ref n3 nil) (ref n2 nil) (ref n1 nil) ) ) 
	)

	)

)

(assert (not 
	(tobool 
		(index alpha1 (skl3 x1 nil )) 
	)

))

(check-sat)
