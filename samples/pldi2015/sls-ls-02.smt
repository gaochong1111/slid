
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



(define-fun llseg ((?E Lst_t) (?len1 Int) (?F Lst_t) (?len2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(=?len1 ?len2)
	)
 
	(exists ((?X Lst_t)  (?d Int) (?len3 Int)) 
	(and  
		(= ?len1 (+ ?len3 1))
		(tobool (ssep 
		(pto ?E (sref (ref next ?X) (ref data ?d)) ) 
		(llseg ?X ?len3 ?F ?len2)
		)
		)
	) 
	)
	)
))


;; slseg(E,F,M1,M2)::= E = F & emp & M1 = M2 | 
;; exists X,M3,v. E |-> ((next,X), (data,v)) * slseg(X,F,M3,M2) & M1={v} cup M3 & v <= M3 |

(define-fun sllseg ((?E Lst_t)  (?len1 Int) (?d1 Int) (?F Lst_t) (?len2 Int) (?d2 Int) ) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?len1 ?len2)
		(= ?d1 ?d2)
	)
 
	(exists ((?X Lst_t)  (?d3 Int) (?len3 Int)) 
	(and (<= ?d1 ?d3) (= ?len1 (+ ?len3 1)) 
		(tobool (ssep 
		(pto ?E (sref (ref next ?X) (ref data ?d1)) ) 
		(sllseg ?X ?len3 ?d3  ?F ?len2 ?d2 )
		)
		)
	) 
	)
	)
))

;; declare variables

(declare-fun X () Lst_t)

(declare-fun len1 () Int)
(declare-fun len2 () Int)


(declare-fun x () Int)
(declare-fun y () Int)

;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)

;;sorted_list(x,len,min) |= list(x,len)

(assert 
	(and 
	(= len2 0)
	(tobool 
		(index alpha1 (sllseg X len1 x nil len2 y))
	)
	)
)

(assert (not 
	(tobool 
		(index alpha2 (llseg X len1 nil len2))
	)
))

(check-sat)
