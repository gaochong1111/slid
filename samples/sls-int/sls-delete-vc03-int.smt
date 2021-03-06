
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
(declare-fun nxt () Lst_t)
(declare-fun keynode () Lst_t)
(declare-fun ret () Lst_t)

(declare-fun X () Lst_t)
(declare-fun Y () Lst_t)

(declare-fun M0 () BagInt)
(declare-fun M1 () BagInt)
(declare-fun M2 () BagInt)
(declare-fun M3 () BagInt)
(declare-fun M4 () BagInt)

(declare-fun key () Int)
(declare-fun d () Int)
(declare-fun d1 () Int)
(declare-fun d2 () Int)
(declare-fun d3 () Int)
(declare-fun d4 () Int)
(declare-fun d5 () Int)

;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)

;; VC03: slseg(root,parent,M1,M2) * parent|->((next,nxt),(data,d)) * slist(X,M4) & M3 = {d2} cup M4 &
;; d2 <= M4 & d <= M3 & 
;; (key in M0 <=> key in M3) & M2 = (M3 cup {d}) \ {key} & M1 = M0 \ {key} & keynode = cur & ! keynode = nil & d2 = key & nxt = X & ret = root
;; |-
;; slist(ret,M1) & key in M0 & M1 = M0 \ {key}



(assert 
	(and
	(tobool 
	(ssep
		(index alpha1 (slseg root d1 parent d2))
		(pto parent (sref (ref next nxt) (ref data d3)))
		(index alpha2 (slseg X d4 nil d5))
	))
	(<=  d2 d3) (<= d3 d4)
	(= nxt X) (= ret root)
	)
)

(assert (not 
	(and 
	(tobool 
		(index alpha3 (slseg ret d1 nil d5))
	)
	)
))

(check-sat)
