
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
(declare-fun cur () Lst_t)
(declare-fun M0 () BagInt)
(declare-fun M1 () BagInt)
(declare-fun key () Int)
(declare-fun d () Int)
(declare-fun ret () Int)

;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)

;; VC4: slseg(root,cur,M0,M1) * slist(cur,M1) & (key in M0 <=> key in M1) & cur = nil & ret = 0 |-
;; slist(root, M0) & ! key in M0 & ret = 0


(assert 
	(and
	(tobool 
	(ssep 
		(index alpha1 (slseg root cur M0 M1) ) 
		(index alpha2 (slist cur M1) )
	))
	(=> (subset (bag key) M0) (subset (bag key) M1) ) 
	(=> (subset (bag key) M1) (subset (bag key) M0) ) 
	(= cur nil)
	(= ret 0)
	)
)

(assert (not 
	(and 
	(tobool 
		(index alpha3 (slist root M0 )) 
	)
	(subset M0 (bagminus M0 (bag key) ) ) 
	(subset (bagminus M0 (bag key) ) M0 ) 
	(= ret 0)
	)
))

(check-sat)
