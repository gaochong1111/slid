
(set-logic QF_S)

;; declare sorts
(declare-sort SL3_t 0)


;; declare fields
(declare-fun n1 () (Field SL3_t SL3_t))
(declare-fun n2 () (Field SL3_t SL3_t))
(declare-fun n3 () (Field SL3_t SL3_t))


;; declare predicates

(define-fun gskl1 ((?hd SL3_t) (?ex SL3_t) ) Space (tospace 
	(or 
	(and (= ?hd ?ex) 
		(tobool emp
		)

	)
 
	(exists ((?tl SL3_t) ) 
	(and (distinct ?hd ?ex) 
		(tobool (ssep 
		(pto ?hd (sref (ref n2 nil) (ref n1 ?tl) ) ) 
		(gskl1 ?tl ?ex )
		) )

	)
 
	)

	)
))

(define-fun gskl2 ((?hd SL3_t) (?ex SL3_t) ) Space (tospace 
	(or 
	(and (= ?hd ?ex) 
		(tobool emp
		)

	)
 
	(exists ((?tl SL3_t) (?Z1 SL3_t) ) 
	(and (distinct ?hd ?ex) 
		(tobool (ssep 
		(pto ?hd (sref (ref n2 ?tl) (ref n1 ?Z1) ) ) 
		(gskl1 ?Z1 ?tl )
		(gskl2 ?tl ?ex )
		) )

	)
 
	)

	)
))

(define-fun gskl3 ((?hd SL3_t) (?ex SL3_t) ) Space (tospace 
	(or 
	(and (= ?hd ?ex) 
		(tobool emp
		)

	)
 
	(exists ((?tl SL3_t) (?Z1 SL3_t) (?Z2 SL3_t) ) 
	(and (distinct ?hd ?ex) 
		(tobool (ssep 
		(pto ?hd (sref (ref n3 ?tl) (ref n2 ?Z2) (ref n1 ?Z1) ) ) 
		(gskl1 ?Z1 ?Z2 )
		(gskl2 ?Z2 ?tl )
		(gskl3 ?tl ?ex )
		) )

	)
 
	)

	)
))

;; declare variables
(declare-fun x1 () SL3_t)
(declare-fun x2 () SL3_t)

;; declare set of locations

(declare-fun alpha0 () SetLoc)

(assert 
	(tobool 
	(ssep 
		(pto x1 (sref (ref n3 x2) (ref n2 x2) (ref n1 x2) ) ) 
		(pto x2 (sref (ref n3 nil) (ref n2 nil) (ref n1 nil) ) ) 
	)

	)

)

(assert (not 
	(tobool 
		(index alpha0 (gskl3 x1 nil )) 
	)

))

(check-sat)
