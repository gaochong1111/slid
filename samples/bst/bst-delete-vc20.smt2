
; Extending QF_S:
; constant emptybag, 
; the function singleton, 
; the multiset comparison operator bag-lt, bag-le, bag-gt, bag-ge
; bag-union, bag-diff, bag-sub

(set-logic QF_S)

;; declare sorts
(declare-sort Bst_t 0)

;; declare fields
(declare-fun left () (Field Bst_t Bst_t))
(declare-fun right () (Field Bst_t Bst_t))
(declare-fun data () (Field Bst_t Int))

;; declare predicates

;; bst(E,M)::= E = nil & emp & M = emptybag | 
;; exists X,Y,M1,M2. E |-> ((left,X), (right,Y)) * bst(X,M1) * bst(Y,M2) & M = {E.data} cup M1 cup M2 & M1 < E.data < M2


(define-fun bst ((?E Bst_t) (?M BagInt)) Space (tospace 
	(or 
	(and (= ?E nil) 
		(tobool emp
		)
		(= ?M emptybag)
	)
 
	(exists ( (?X Bst_t) (?Y Bst_t) (?M1 BagInt) (?M2 BagInt) (?d Int) ) 
	(and (distinct ?E nil) 
		(tobool (ssep 
		(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d)) ) 
		(bst ?X ?M1)
		(bst ?Y ?M2)
		)
		)
		(= ?M (bag-union (singleton ?d) (bag-union ?M1 ?M2) ) )
		(bag-lt ?M1 (singleton ?d))
		(bag-lt (singleton ?d) ?M2)
	)
	)
	)
))

;; bsthole(E,F,M1,M2)::= E = F & emp & M1 = M2 | 
;; exists X,Y,M3,M4. E |-> ((left,X), (right,Y)) * bst(X,M3) * bsthole(Y,F,M4,M2) & M1={E.data} cup M3 cup M4 & M3 < E.data < M4 |
;; exists X,Y,M3,M4. E |-> ((left,X), (right,Y)) * bsthole(X,F,M3,M2) * bst(Y,M4) & M1={E.data} cup M3 cup M4 & M3 < E.data < M4

(define-fun bsthole ((?E Bst_t) (?F Bst_t) (?M1 BagInt) (?M2 BagInt)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?M1 ?M2)
	)
 
	(exists ((?X Bst_t) (?Y Bst_t) (?M3 BagInt) (?M4 BagInt) (?d Int)) 
	(and (distinct ?E ?F) 
		(tobool (ssep 
		(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d)) ) 
		(bst ?X ?M3)
		(bsthole ?Y ?F ?M4 ?M2)
		)
		)
		(= ?M1  (bag-union (singleton ?d) (bag-union ?M3 ?M4) ) )
		(bag-lt ?M3 (singleton ?d) )
		(bag-lt (singleton ?d) ?M4 )
	) 
	)

	(exists ((?X Bst_t) (?Y Bst_t) (?M3 BagInt) (?M4 BagInt) (?d Int)) 
	(and (distinct ?E ?F) 
		(tobool (ssep 
		(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d)) ) 
		(bsthole ?X ?F ?M3 ?M2)
		(bst ?Y ?M4)
		)
		)
		(= ?M1 (bag-union (singleton ?d) (bag-union ?M3 ?M4) ) )
		(bag-lt ?M3 (singleton ?d) )
		(bag-lt (singleton ?d) ?M4 )
	) 
	)
	)
))

;; declare variables
;; (declare-fun root0 () Bst_t)
(declare-fun cur () Bst_t)
(declare-fun rgt () Bst_t)
(declare-fun parent () Bst_t)
(declare-fun subroot () Bst_t)
(declare-fun nxtparent () Bst_t)
(declare-fun X () Bst_t)
(declare-fun Z () Bst_t)
(declare-fun U () Bst_t)
(declare-fun V () Bst_t)

(declare-fun M0 () BagInt)
(declare-fun M1 () BagInt)
(declare-fun M2 () BagInt)
(declare-fun M3 () BagInt)
(declare-fun M4 () BagInt)
(declare-fun M5 () BagInt)
(declare-fun M6 () BagInt)
(declare-fun M7 () BagInt)
(declare-fun M8 () BagInt)
(declare-fun M9 () BagInt)
(declare-fun key () Int)
(declare-fun keymin () Int)
(declare-fun d2 () Int)
(declare-fun d3 () Int)

;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)
(declare-fun alpha5 () SetLoc)
(declare-fun alpha6 () SetLoc)

;; VC20: bst(X, M1) * bsthole(rgt, nxtparent, M5, M6) * nxtparent |-> ((left, V), (right, Z), (data, d2)) * 
;; cur |-> ((left,X), (right,rgt), (data,d3)) * bst(U, M8) * bst(V, M9) * bst(Z, M4) & M3 = {d3} cup M8 cup M9 & 
;; M8 < d3 < M9 & M6 = ({d2} cup M3 cup M4) \ {keymin} & M3 < d2 < M4 & M0 = {key} cup M1 cup M5 cup {keymin} & 
;; M1 < key < M5 cup {keymin} & parent = nil & ! cur = nil & keymin in M3 & keymin <= M3 & U = nil & subroot = cur &
;; M7 = {d3} cup M1 cup M5 |-
;; bst(subroot, M7) & key in M0 & M7 = M0 \ {key} & parent = nil

(assert 
	(and
	(tobool 
	(ssep 
		(index alpha1 (bst X M1) )
		(index alpha2 (bsthole rgt nxtparent M5 M6) )
		(pto nxtparent (sref (ref left V) (ref right Z) (ref data d2) ) )
		(pto cur (sref (ref left X) (ref right rgt) (ref data d3) ) )
		(index alpha3 (bst U M8)) 
		(index alpha4 (bst V M9) )
		(index alpha5 (bst Z M4) )
	))
	(= M3 (bag-union (singleton d3) (bag-union M8 M9))
	(< M8 (singleton d3) )
	(< (singleton d) M9)
	(= M6 (bag-diff (bag-union (singleton d2) (bag-union M3 M4)) (singleton keymin)) )
	(< M3 (singleton d3) )
	(< (singleton d) M4)
	(= M0 (bag-union (singleton key) (bag-union M1 (bag-union M5 (singleton keymin)))
	(< M1 (singleton key) )
	(< (singleton key) (bag-union M5 (singleton keymin)) )
	(= parent nil)
	(distinct cur nil)
	(bag-sub (singleton keymin) M3)
	(<= (singleton keymin) M3)
	(= U nil)
	(= subroot cur)
	(= M7 (bag-union (singleton d3) (bag-union M1 M5)) )
	)
)

;; bst(subroot, M7) & key in M0 & M7 = M0 \ {key} & parent = nil

(assert (not 
	(and
	(tobool 
		(index alpha6 (bst subroot M7) )
	)
	(bag-sub (singleton key) M0)
	(= M7 (bag-diff M0 (singleton key)) )
	(= parent nil)
	)
))

(check-sat)
