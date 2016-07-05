
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

(declare-fun M0 () BagInt)
(declare-fun M1 () BagInt)
(declare-fun M2 () BagInt)
(declare-fun M3 () BagInt)

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

;; VC03: root |-> ((next,X), (data,d)) * slist(X,M1) & cur1 = root & parent1 = nil & M0 =  {d} cup M1 & d <= M1 & 
;; d < key & parent2 = cur1 & cur2 = X
;; M2 = M3 & M2 = ite(key in M0, M0, M0 cup {key})
;; |-  slseg(root,parent2,M2,M3) * parent2 |-> ((next,cur2),(data,d)) * slist(cur2,M1) & d <= M1 & (key in M0 <=> key in M1) & 
;; M3 = ite(key in M1, M1 cup {d}, M1 cup {d} cup {key}) & M2 = ite(key in M0, M0, M0 cup {key})

(assert 
	(and
	(tobool 
	(ssep
		(pto root (sref (ref next X) (ref data d)) )
		(index alpha1 (slseg X d1 nil d2))
	))
	(= cur1 root)
	(<= d d1)
	(= parent1 nil)  (= parent2 cur1) (= cur2 X)
	)
)

(assert (not 
	(and 
	(tobool 
	(ssep
		(index alpha2 (slseg root d parent2 d))
		(pto parent2 (sref (ref next cur2) (ref data d)))
		(index alpha3 (slseg cur2 d1 nil d2))
	))
	)
))

(check-sat)