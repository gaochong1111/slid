
; Extending QF_S:
; constant emptybag, 
; the function singleton, 
; the multiset comparison operator bag-lt, bag-le, bag-gt, bag-ge
; bag-union, bag-diff, bag-sub

(set-logic QF_SLRDI)

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
		(= ?M (bagunion (bag ?d) ?M1 ?M2) )
		(< ?M1 (bag ?d))
		(< (bag ?d) ?M2)
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
		(= ?M1  (bagunion (bag ?d) ?M3 ?M4) )
		(< ?M3 (bag ?d) )
		(< (bag ?d) ?M4 )
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
		(= ?M1 (bagunion (bag ?d) ?M3 ?M4) )
		(< ?M3 (bag ?d) )
		(< (bag ?d) ?M4 )
	) 
	)
	)
))

;; declare variables
(declare-fun root0 () Bst_t)
(declare-fun X () Bst_t)
(declare-fun Y () Bst_t)
(declare-fun cur1 () Bst_t)
(declare-fun cur2 () Bst_t)
(declare-fun parent1 () Bst_t)
(declare-fun parent2 () Bst_t)
(declare-fun M0 () BagInt)
(declare-fun M1 () BagInt)
(declare-fun M2 () BagInt)
(declare-fun key () Int)
(declare-fun d () Int)

;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)

;; VC03: root0|->((left,X), (right,Y), (data, d)) * bst(X, M1) * bst(Y, M2) & M0 = {d} cup M1 cup M2 & M1 < d < M2 & d < key & cur1 = root0 & 
;; parent1 = nil & ! root0 = nil & parent2 = cur1 & cur2 = Y |-
;; root0|->((left,X), (right,cur2), (data, d)) * bst(X, M1) * bst(cur2, M2) & M0 = {d} cup M1 cup M2 & M1 < d < M2 & cur1 = root0 & parent2 = cur1 & 
;; key in M0 <=> key in M2  & ! parent2 = nil

(assert 
	(and
	(tobool 
	(ssep 
		(pto root0 (sref (ref left X) (ref right Y) (ref data d) ) ) 
		(index alpha1 (bst X M1) )
		(index alpha2 (bst Y M2) )
	))
	(= M0 (bagunion (bag d) M1 M2))
	(< M1 (bag d) )
	(< (bag d) M2)
	(< d key)
	(= cur1 root0)
	(= parent1 nil)
	(distinct root0 nil)
	(= parent2 cur1)
	(= cur2 Y)
	)
)

;; root0|->((left,X), (right,cur2), (data, d)) * bst(X, M1) * bst(cur2, M2) & M0 = {d} cup M1 cup M2 & M1 < d < M2 & cur1 = root0 & parent2 = cur1 & 
;; key in M0 <=> key in M2  & ! parent2 = nil

(assert (not 
	(and
	(tobool 
	(ssep 
		(pto root0 (sref (ref left X) (ref right cur2) (ref data d) ) ) 
		(index alpha3 (bst X M1) )
		(index alpha4 (bst cur2 M2) )
	))
	(= M0 (bagunion (bag d) M1 M2)) 
	(< M1 (bag d) )
	(< (bag d) M2)
	(= cur1 root0)
	(= parent2 cur1)
	(=> (subset (bag key) M0) (subset (bag key) M2) )
	(=> (subset (bag key) M2) (subset (bag key) M0) )
	(distinct parent2 nil)
	)
))

(check-sat)
