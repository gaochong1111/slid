
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



(define-fun lseg ((?E Lst_t) (?F Lst_t)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
	)
 
	(exists ((?X Lst_t)  (?d Int)) 
	(and  
		(tobool (ssep 
		(pto ?E (sref (ref next ?X) (ref data ?d)) ) 
		(lseg ?X ?F)
		)
		)
	) 
	)
	)
))


;; slseg(E,F,M1,M2)::= E = F & emp & M1 = M2 | 
;; exists X,M3,v. E |-> ((next,X), (data,v)) * slseg(X,F,M3,M2) & M1={v} cup M3 & v <= M3 |

(define-fun slseg ((?E Lst_t) (?d1 Int) (?F Lst_t) (?d2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?d1 ?d2)
	)
 
	(exists ((?X Lst_t)  (?d3 Int)) 
	(and (<= ?d1 ?d3) 
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

(declare-fun X () Lst_t)

(declare-fun x () Int)
(declare-fun y () Int)

;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)

;;sorted_list(x,min) |= list(x)
;; sorted_list(x,min) == slseg(x,min,nil,max)
;; list(x) == lseg(x,nil)

(assert 
	(tobool 
		(index alpha1 (slseg X x nil y))
	)
)

(assert (not 
	(tobool 
		(index alpha2 (lseg X nil))
	)
))

(check-sat)
