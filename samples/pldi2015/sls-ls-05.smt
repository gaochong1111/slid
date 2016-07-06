
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
(declare-fun prev () (Field Lst_t Lst_t))
(declare-fun data () (Field Lst_t Int))


(define-fun sldllseg ((?E Lst_t)  (?P Lst_t) (?len1 Int) (?d1 Int) (?F Lst_t) (?L Lst_t) (?len2 Int) (?d2 Int) ) Space (tospace 
	(or 
	(and (= ?E ?F) (= ?P ?L)
		(= ?len1 ?len2)
		(= ?d1 ?d2) 
		(tobool emp
		)
	)
 
	(exists ((?X Lst_t)  (?d3 Int) (?len3 Int)) 
	(and (<= ?d1 ?d3) (= ?len1 (+ ?len3 1)) 
		(tobool (ssep 
		(pto ?E (sref (ref next ?X) (ref prev ?P) (ref data ?d1)) ) 
		(sldllseg ?X ?E ?len3 ?d3  ?F ?L ?len2 ?d2 )
		)
		)
	) 
	)
	)
))

;; declare variables

(declare-fun X () Lst_t)
(declare-fun Y () Lst_t)
(declare-fun Z () Lst_t)
(declare-fun P () Lst_t)
(declare-fun L () Lst_t)
(declare-fun M () Lst_t)


(declare-fun len1 () Int)
(declare-fun len2 () Int)
(declare-fun len3 () Int)


(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun u () Int)


;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)


(assert 
	(and 
	(<= y z)
	(tobool 
		(ssep 
		(index alpha1 (sldllseg X P len1 x Y L len2 y))
		(index alpha2 (sldllseg Y L len2 z Z M len3 u))
		)
	)
	)
)

(assert (not 
	(tobool 
		(index alpha3 (sldllseg X P len1 x Z M len3 u))
	)
))

;the result is sat, consider the both empty case

(check-sat)
