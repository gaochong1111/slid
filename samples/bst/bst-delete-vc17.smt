
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
(declare-fun parent () Bst_t)
(declare-fun keynode () Bst_t)
(declare-fun rgt () Bst_t)
(declare-fun nxtparent1 () Bst_t)
(declare-fun nxtparent2 () Bst_t)

(declare-fun X () Bst_t)
(declare-fun Y () Bst_t)
(declare-fun Z () Bst_t)
(declare-fun U () Bst_t)

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
(declare-fun d1 () Int)
(declare-fun d2 () Int)
(declare-fun d3 () Int)

;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)
(declare-fun alpha5 () SetLoc)
(declare-fun alpha6 () SetLoc)
(declare-fun alpha7 () SetLoc)
(declare-fun alpha8 () SetLoc)
(declare-fun alpha9 () SetLoc)

;; VC17: keynode |-> ((left, X), (right, rgt), (data, key)) * bst(X, M1) * bsthole(rgt, nxtparent1, M5, M6) * 
;; nxtparent1 |-> ((left, cur1), (right, Z), (data, d2)) * cur1 |-> ((left,U),(right,Y),(data,d3)) * bst(U,M8) * bst(Y,M9) * 
;; bst(Z, M4) & M3 = {d3} cup M8 cup M9 & M8 < d3 < M9 & M6 = ({d2} cup M3 cup M4) \ {keymin} & M3 < d2 < M4 & 
;; M0 = {key} cup M1 cup M5 cup {keymin} & M1 < key < M5 cup {keymin} & parent = nil & ! cur1 = nil & keymin in M3 & keymin <= M3 & 
;; !U = nil & nxtparent2 = cur1 & cur2 = U & M7 = ({d3} cup M8 cup M9) \ {keymin} |-
;; keynode |-> ((left, X), (right, rgt), (data, key)) * bst(X, M1) * bsthole(rgt, nxtparent2, M5, M7) * 
;; nxtparent2 |-> ((left, cur2), (right, Y), (data, d3)) * bst(cur2, M8) * bst(Y, M9) & M7 = ({d3} cup M8 cup M9) \ {keymin} & 
;; M8 < d3 < M9 & M0 = {key} cup M1 cup M5 cup {keymin} & M1 < key < M5 cup {keymin} & parent = nil & ! cur2 = nil & 
;; keymin in M8 & keymin <= M8

(assert 
	(and
	(tobool 
	(ssep 
		(pto keynode (sref (ref left X) (ref right rgt) (ref data key) ) ) 
		(index alpha1 (bst X M1))
		(index alpha2 (bsthole rgt nxtparent1 M5 M6))
		(pto nxtparent1 (sref (ref left cur1) (ref right Z) (ref data d2) ) ) 
		(pto cur1 (sref (ref left U) (ref right Y) (ref data d3) ) ) 
		(index alpha3 (bst U M8) )
		(index alpha4 (bst Y M9) )
		(index alpha5 (bst Z M4) )
	))
	(= M3 (bagunion (bag d3) M8 M9) ) 
	(< M8 (bag d3) )
	(< (bag d3) M9)
	(= M6 (bagminus (bagunion (bag d2) M3 M4) (bag keymin)) )
	(< M3 (bag d2) )
	(< (bag d2) M4 )
	(= M0 (bagunion (bag key) M1 M5 (bag keymin) ) ) (< M1 (bag key))  (< (bag key) (bagunion M5 (bag keymin)) )
	(= parent nil) (distinct cur1 nil) (subset (bag keymin) M3) (<= (bag keymin) M3) 
	(distinct U nil)
	(= nxtparent2 cur1)
	(= cur2 U)
	(= M7 (bagminus (bagunion (bag d3) M8 M9) (bag keymin)) )
	)
)

;; keynode |-> ((left, X), (right, rgt), (data, key)) * bst(X, M1) * bsthole(rgt, nxtparent2, M5, M7) * 
;; nxtparent2 |-> ((left, cur2), (right, Y), (data, d3)) * bst(cur2, M8) * bst(Y, M9) & M7 = ({d3} cup M8 cup M9) \ {keymin} & 
;; M8 < d3 < M9 & M0 = {key} cup M1 cup M5 cup {keymin} & M1 < key < M5 cup {keymin} & parent = nil & ! cur2 = nil & 
;; keymin in M8 & keymin <= M8

(assert (not 
	(and
	(tobool 
	(ssep 
		(pto keynode (sref (ref left X) (ref right rgt) (ref data key) ) ) 
		(index alpha6 (bst X M1) )
		(index alpha7 (bsthole rgt nxtparent2 M5 M7) )
		(pto nxtparent2 (sref (ref left cur2) (ref right Y) (ref data d3) ) ) 
		(index alpha8 (bst cur2 M8) )
		(index alpha9 (bst Y M9) )		
	))
	(= M7 (bagminus (bagunion (bag d3) M8 M9) (bag keymin) ) )
	(< M8 (bag d3) )
	(< (bag d3) M9)
	(= M0 (bagunion (bag key) M1 M5 (bag keymin) ) )
	(< M1 (bag key) )
	(< (bag key) (bagunion M5 (bag keymin)) ) 
	(= parent nil)
	(distinct cur2 nil)
	(subset (bag keymin) M8)
	(<= (bag keymin) M8)
	)
))

(check-sat)
