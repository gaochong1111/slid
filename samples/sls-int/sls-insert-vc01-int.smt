
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

(define-fun slseg ((?E Lst_t) (?d1 Int)  (?F Lst_t) (?d2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?d1 ?d2)
	)
 
	(exists ((?X Lst_t)  (?d3 Int)) 
	(and  (<= ?d1 ?d3)
		(tobool (ssep 
		(pto ?E (sref (ref next ?X) (ref data ?d1)) ) 
		(slseg ?X ?d3 ?F ?d2)
		)
		)
		
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


(declare-fun key () Int)
(declare-fun d () Int)


;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)

;; VC01: x |-> ((next,nil),(data,key)) & root1 = nil & root2 = x & M1 = {key}
;; |-  slist(root2,M1) & M1 = {key}


(assert 
	(and
	(tobool 
		(pto X (sref (ref next nil) (ref data key)) )
	)
	(= root1 nil)
	(= root2 X)
	(<= key d)
	)
)

(assert (not 
	(and 
	(tobool 
		(index alpha1 (slseg root2 key nil d)) 
	)
	)
))

(check-sat)
