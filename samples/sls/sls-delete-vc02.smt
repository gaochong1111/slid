
; Extending QF_S:
; constant emptybag, 
; the function bag, 
; the multiset comparison operator <=, bag-le, bag-gt, bag-ge
; bagunion, intersection, difference of multisets
; an element is contained in a multiset

(set-logic QF_SLRDI)

;; declare sorts
(declare-sort Lst_t 0)

;; declare fields
(declare-fun next () (Field Lst_t Lst_t))
(declare-fun data () (Field Lst_t Int))

;; declare predicates

;; slist(E,M)::= E = nil & emp & M = emptyset | 
;; exists X,M1,v. E |-> ((next,X),(data,v)) * slist(X,M1) & M={v} cup M1 & v <= M1


(define-fun slist ((?E Lst_t) (?M BagInt)) Space (tospace 
	(or 
	(and (= ?E nil) 
		(tobool emp
		)
		(= ?M emptybag)
	)
 
	(exists ( (?X Lst_t) (?M1 BagInt) (?d Int) ) 
	(and (distinct ?E nil) 
		(tobool (ssep 
		(pto ?E (sref (ref next ?X) (ref data ?d)) ) 
		(slist ?X ?M1)
		)
		)
		(= ?M (bagunion (bag ?d) ?M1 ) )
		(<= (bag ?d) ?M1)
	)
	)
	)
))

;; slseg(E,F,M1,M2)::= E = F & emp & M1 = M2 | 
;; exists X,M3,v. E |-> ((next,X), (data,v)) * slseg(X,F,M3,M2) & M1={v} cup M3 & v <= M3 |

(define-fun slseg ((?E Lst_t) (?F Lst_t) (?M1 BagInt) (?M2 BagInt)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?M1 ?M2)
	)
 
	(exists ((?X Lst_t)  (?M3 BagInt) (?d Int)) 
	(and (distinct ?E ?F) 
		(tobool (ssep 
		(pto ?E (sref (ref next ?X) (ref data ?d)) ) 
		(slseg ?X ?F ?M3 ?M2)
		)
		)
		(= ?M1  (bagunion (bag ?d)  ?M3 ) )
		(<= (bag ?d) ?M3 )
	) 
	)
	)
))

;; declare variables
(declare-fun root () Lst_t)
(declare-fun root1 () Lst_t)
(declare-fun root2 () Lst_t)
(declare-fun cur () Lst_t)
(declare-fun cur1 () Lst_t)
(declare-fun cur2 () Lst_t)
(declare-fun parent () Lst_t)
(declare-fun parent1 () Lst_t)
(declare-fun parent2 () Lst_t)

(declare-fun X () Lst_t)
(declare-fun Y () Lst_t)

(declare-fun M0 () BagInt)
(declare-fun M1 () BagInt)
(declare-fun M2 () BagInt)
(declare-fun M3 () BagInt)
(declare-fun M4 () BagInt)
(declare-fun M5 () BagInt)

(declare-fun key () Int)
(declare-fun ret () Int)
(declare-fun d () Int)
(declare-fun d1 () Int)
(declare-fun d2 () Int)

;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)

;; VC02: slseg(root,parent1,M1,M2) * parent1|->((next,cur1),(data,d1)) * cur1|->((next,X),(data,d2))* slist(X,M5) & M3 = {d2} cup M5
;; & d2 <= M5 & d1 <= M3 & (key in M0 <=> key in M3) & M2 = (M3 cup {d1}) \ {key} & M1 = M0 \ {key} & cur1 != nil & d2 < key & parent2 = cur1 &
;; cur2 = X & M4 = (M5 cup {d2}) \ {key}
;; |-
;; slseg(root,parent2,M1,M4) * parent2|->((next,cur2),(data,d2)) * slist(cur2,M5) & d2 <= M5 & 
;; (key in M0 <=> key in M5) & M4 = (M5 cup {d2}) \ {key} & M1 = M0 \ {key}



(assert 
	(and
	(tobool 
	(ssep
		(index alpha1 (slseg root parent1 M1 M2))
		(pto parent1 (sref (ref next cur1) (ref data d1)))
		(pto cur1 (sref (ref next X) (ref data d2)))
		(index alpha2 (slist X M5))
	))
	(= M3 (bagunion (bag d2) M5) )
	(<= (bag d2) M5) (<= (bag d1) M3)
	(=> (subset (bag key) M0) (subset (bag key) M3) ) 
	(=> (subset (bag key) M3) (subset (bag key) M0) ) 
	(= M2 (bagminus (bagunion M3 (bag d1)) (bag key) ) )
	(= M1 (bagminus M0 (bag key)) ) (distinct cur1 nil) (< d2 key) (= parent2 cur1)
	(= cur2 X) (= M4 (bagminus (bagunion M5 (bag d2)) (bag key) ) )
	)
)

(assert (not 
	(and 
	(tobool 
	(ssep
		(index alpha3 (slseg root parent2 M1 M4))
		(pto parent2 (sref (ref next cur2) (ref data d2)))
		(index alpha4 (slist cur2 M5))
	))
	(<= (bag d2) M5)	
	(=> (subset (bag key) M0) (subset (bag key) M5) ) 
	(=> (subset (bag key) M5) (subset (bag key) M0) ) 
	(= M4 (bagminus (bagunion M5 (bag d2)) (bag key) ) )
	(= M1 (bagminus M0 (bag key)) )
	)
))

(check-sat)
