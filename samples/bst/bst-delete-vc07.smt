
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
(declare-fun cur1 () Bst_t)
(declare-fun cur2 () Bst_t)
(declare-fun parent1 () Bst_t)
(declare-fun parent2 () Bst_t)
(declare-fun X () Bst_t)
(declare-fun Y () Bst_t)
(declare-fun Z () Bst_t)
(declare-fun M0 () BagInt)
(declare-fun M1 () BagInt)
(declare-fun M2 () BagInt)
(declare-fun M3 () BagInt)
(declare-fun M4 () BagInt)
(declare-fun M5 () BagInt)
(declare-fun M6 () BagInt)
(declare-fun M7 () BagInt)
(declare-fun key () Int)
(declare-fun d1 () Int)
(declare-fun d2 () Int)

;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)
(declare-fun alpha5 () SetLoc)
(declare-fun alpha6 () SetLoc)
(declare-fun alpha7 () SetLoc)

;; VC07: bsthole(root0, parent1, M1, M2) * parent1 |-> ((left,X), (right,cur1), (data, d1)) * bst(X,M3) * 
;; cur1 |-> ((left,Z), (right,Y), (data, d2)) * bst(Z, M6) * bst(Y, M7) & M1 = M0 \ {key} & M2 = ({d1} cup M3 cup M4) \ {key} & 
;; M3 < d1 < M4 & M3 = {d2} cup M6 cup M7 & M6 < d2 < M7 & ! parent1 =nil & d1 < key & (key in M0 <=> key in M4) & ! cur1 = nil & 
;; d2 < key & parent2 = cur1 & cur2 = Y & M5 = M3 \ {key} |-
;; bsthole(root0,parent2, M1, M5) * parent2 |-> ((left,Z), (right,cur2), (data, d2)) * bst(Z, M6) * bst(cur2, M7) & M1 = M0 \ {key} &
;; M5 = ({d2} cup M6 cup M7) \ {key}  & M6 < d2 < M7  & !(parent2 = nil) & d2 < key & key in M0 <=> key in M7

(assert 
	(and
	(tobool 
	(ssep 
		(index alpha1 (bsthole root0 parent1 M1 M2) )
		(pto parent1 (sref (ref left X) (ref right cur1) (ref data d1) ) )
		(index alpha2 (bst X M3)) 
		(pto cur1 (sref (ref left Z) (ref right Y) (ref data d2) ) ) 
		(index alpha3 (bst Z M6) )
		(index alpha4 (bst Y M7) )
	))
	(= M1 (bagminus M0 (bag key)) )
	(= M2 (bagminus (bagunion (bag d1) M3 M4) (bag key)) )
	(< M3 (bag d1) )
	(< (bag d1) M4)
	(= M3 (bagunion (bag d2) M6 M7))
	(< M6 (bag d2) )
	(< (bag d2) M7)
	(distinct parent1 nil)
	(> d1 key)
	(=> (subset (bag key) M0) (subset (bag key) M4))
	(=> (subset (bag key) M4) (subset (bag key) M0))
	(distinct cur1 nil)
	(< d2 key)
	(= parent2 cur1)
	(= cur2 Y)
	(= M5 (bagminus M3 (bag key)))
	)
)

;; bsthole(root0,parent2, M1, M5) * parent2 |-> ((left,Z), (right,cur2), (data, d2)) * bst(Z, M6) * bst(cur2, M7) & M1 = M0 \ {key} &
;; M5 = ({d2} cup M6 cup M7) \ {key}  & M6 < d2 < M7  & !(parent2 = nil) & d2 < key & key in M0 <=> key in M7

(assert (not 
	(and
	(tobool 
	(ssep 
		(index alpha5 (bsthole root0 parent2 M1 M5) )
		(pto parent2 (sref (ref left Z) (ref right cur2) (ref data d2) ) ) 
		(index alpha6 (bst Z M6) )
		(index alpha7 (bst cur2 M7) )
	))
	(= M1 (bagminus M0 (bag key)) )
	(= M5 (bagminus (bagunion (bag d2) M6 M7) (bag key)) )
	(< M6 (bag d2) )
	(< (bag d2) M7)
	(distinct parent2 nil)
	(< d2 key)
	(=> (subset (bag key) M0) (subset (bag key) M7) )
	(=> (subset (bag key) M7) (subset (bag key) M0) )
	)
))

(check-sat)
