
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
(declare-fun nxtparent () Bst_t)

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

(declare-fun key () Int)
(declare-fun keymin () Int)
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

;; VC14: root0|->((left,X), (right,Y), (data, d1)) * bst(X, M1) * Y |-> ((left, U),(right,Z), (data, d2)) * bst(U, M3) * 
;; bst(Z, M4) & M2 = {d2} cup M3 cup M4 & M3 < d2 < M4 & M0 = {d1} cup M1 cup M2 & M1 < d1 < M2 & cur1 = root0 & parent = nil & 
;; key = d1 & keynode = cur1 & d1 = key & !Y = nil & rgt = Y & !Z = nil & cur2 = U & nxtparent = rgt & M5 = M6 & 
;; M6 = ({d2} cup M3 cup M4) \ {keymin} & keymin in M3 & keymin <= M3 |-
;; keynode |-> ((left, X), (right, rgt), (data, key)) * bst(X, M1) * bsthole(rgt, nxtparent, M5, M6) * 
;; nxtparent |-> ((left, cur2), (right, Z), (data, d2)) * bst(cur2, M3) * bst(Z, M4) & M6 = ({d2} cup M3 cup M4) \ {keymin} & 
;; M3 < d2 < M4 & M0 = {key} cup M1 cup M5 cup {keymin} & M1 < key < M5 cup {keymin} & parent = nil & ! cur2 = nil & 
;; keymin in M3 & keymin <= M3

(assert 
	(and
	(tobool 
	(ssep 
		(pto root0 (sref (ref left X) (ref right Y) (ref data d1) ) ) 
		(index alpha1 (bst X M1))
		(pto Y (sref (ref left U) (ref right Z) (ref data d2) ) ) 
		(index alpha2 (bst U M3) )
		(index alpha3 (bst Z M4) )
	))
	(= M2 (bagunion (bag d2) M3 M4) ) 
	(< M3 (bag d2) )
	(< (bag d2) M4)
	(= M0 (bagunion (bag d1) M1 M2) ) 
	(< M1 (bag d1) )
	(< (bag d1) M2 )
	(= cur1 root0)
	(= parent nil)
	(= key d1)
	(= keynode cur1)
	(= d1 key)
	(distinct Y nil)
	(= rgt Y)
	(distinct Z nil)
	(= cur2 U)
	(= nxtparent rgt)
	(= M5 M6)
	(= M6 (bagminus (bagunion (bag d2) M3 M4) (bag keymin) ) )
	(subset (bag keymin) M3)
	(<= (bag keymin) M3)
	)
)

;; keynode |-> ((left, X), (right, rgt), (data, key)) * bst(X, M1) * bsthole(rgt, nxtparent, M5, M6) * 
;; nxtparent |-> ((left, cur2), (right, Z), (data, d2)) * bst(cur2, M3) * bst(Z, M4) & M6 = ({d2} cup M3 cup M4) \ {keymin} & 
;; M3 < d2 < M4 & M0 = {key} cup M1 cup M5 cup {keymin} & M1 < key < M5 cup {keymin} & parent = nil & ! cur2 = nil & 
;; keymin in M3 & keymin <= M3

(assert (not 
	(and
	(tobool 
	(ssep 
		(pto keynode (sref (ref left X) (ref right rgt) (ref data key) ) ) 
		(index alpha4 (bst X M1) )
		(index alpha5 (bsthole rgt nxtparent M5 M6) )
		(pto nxtparent (sref (ref left cur2) (ref right Z) (ref data d2) ) ) 
		(index alpha6 (bst cur2 M3) )
		(index alpha7 (bst Z M4) )		
	))
	(= M6 (bagminus (bagunion (bag d2) M3 M4) (bag key) ) )
	(< M3 (bag d2) )
	(< (bag d2) M4)
	(= M0 (bagunion (bag key) M1 M5 (bag keymin) ) )
	(< M1 (bag key) )
	(< (bag key) (bagunion M5 (bag keymin)) ) 
	(= parent nil)
	;;(distinct cur2 nil)
	(subset (bag keymin) M3)
	(<= (bag keymin) M3)
	)
))

(check-sat)
