
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
(declare-fun M10 () BagInt)
(declare-fun M11 () BagInt)
(declare-fun M12 () BagInt)

(declare-fun key () Int)
(declare-fun keymin () Int)
(declare-fun d1 () Int)
(declare-fun d2 () Int)
(declare-fun d3 () Int)
(declare-fun d4 () Int)

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
(declare-fun alpha10 () SetLoc)
(declare-fun alpha11 () SetLoc)
(declare-fun alpha12 () SetLoc)
(declare-fun alpha13 () SetLoc)

;; VC18: bsthole(root0, parent, M1, M2) * parent |-> ((left, keynode), (right,Y), (data, d1)) * 
;; keynode |-> ((left,X), (right, rgt), (data, key)) * bst(X,M5) * bsthole(rgt, nxtparent1, M8, M9) * 
;; nxtparent1 |-> ((left, cur1), (right, Z), (data, d3)) * cur1 |-> ((left, V), (right, U), (data, d4)) * bst(V, M11) * 
;; bst(U, M12) * bst(Z, M7) * bst(Y,M4) & M6 = {d4} cup M11 cup M12 & M11 < d4 < M12 & M5 < key < M8 cup {keymin} & 
;; M9 = ({d3} cup M6 cup M7) \ {keymin} & M6 < d3 < M7 & M3 = {key} cup M5 cup M8 cup {keymin} & key in M0 & M1 = M0 \ {key} & 
;; M2 = ({d1} cup M3 cup M4) \ {key} & M3 < d1 < M4 & !(parent = nil) & d1 > key & ! cur1 = nil & keymin in M6 & keymin <= M6 & 
;; ! V = nil & nxtparent = cur1 & cur2 = V & M10 = M6 \ {keymin} |-
;; bsthole(root0, parent, M1, M2) * parent |-> ((left, keynode), (right,Y), (data, d1)) * 
;; keynode |-> ((left,X), (right, rgt), (data, key)) * bst(X,M5) * bsthole(rgt, nxtparent2, M8, M10) * 
;; nxtparent2 |-> ((left, cur2), (right, U), (data, d4)) * bst(cur2, M11) * bst(U, M12) * bst(Y,M4) & M5 < key < M8 cup {keymin} & 
;; M10 = ({d4} cup M11 cup M12) \ {keymin} & M11 < d4 < M12 & M3 = {key} cup M5 cup M8 cup {keymin} & key in M0 & M1 = M0 \ {key} &
;; M2 = ({d1} cup M3 cup M4) \ {key} & M3 < d1 < M4 & !(parent = nil) & d1 > key & ! cur2 = nil & keymin in M11 & keymin <= M11


(assert 
	(and
	(tobool 
	(ssep 
		(index alpha1 (bsthole root0 parent M1 M2))
		(pto parent (sref (ref left keynode) (ref right Y) (ref data d1) ) ) 
		(pto keynode (sref (ref left X) (ref right rgt) (ref data key) ) ) 
		(index alpha2 (bst X M5) )
		(index alpha3 (bsthole rgt nxtparent1 M8 M9) )
		(pto nxtparent1 (sref (ref left cur1) (ref right Z) (ref data d3) ) ) 
		(pto cur1 (sref (ref left V) (ref right U) (ref data d4) ) ) 
		(index alpha4 (bst V M11) )
		(index alpha5 (bst U M12) )
		(index alpha6 (bst Z M7) )
		(index alpha7 (bst Y M4) )
	))
	(= M6 (bagunion (bag d4) M11 M12) ) 
	(< M11 (bag d4) )
	(< (bag d4) M12)
	(< M5 (bag key) )
	(< (bag d2) (bagunion M8 (bag keymin)) )
	(= M9 (bagminus (bagunion (bag d3) M6 M7) (bag keymin)) )
	(< M6 (bag d3) )
	(< (bag d3) M7)
	(= M3 (bagunion (bag key) M5 M8 (bag keymin)) )
	(subset (bag key) M0)
	(= M1 (bagminus M0 (bag key)))
	(= M2 (bagminus (bagunion (bag d1) M3 M4) (bag key) ) )
	(< M3 (bag d1))
	(< (bag d1) M4)
	(distinct parent nil)
	(> d1 key)
	(distinct cur1 nil)
	(subset (bag keymin) M6)
	(<= (bag keymin) M6)
	(distinct V nil)
	(= nxtparent2 cur1)
	(= cur2 V)
	(= M10 (bagminus M6 (bag keymin)))
	)
)

;; bsthole(root0, parent, M1, M2) * parent |-> ((left, keynode), (right,Y), (data, d1)) * 
;; keynode |-> ((left,X), (right, rgt), (data, key)) * bst(X,M5) * bsthole(rgt, nxtparent2, M8, M10) * 
;; nxtparent2 |-> ((left, cur2), (right, U), (data, d4)) * bst(cur2, M11) * bst(U, M12) * bst(Y,M4) & M5 < key < M8 cup {keymin} & 
;; M10 = ({d4} cup M11 cup M12) \ {keymin} & M11 < d4 < M12 & M3 = {key} cup M5 cup M8 cup {keymin} & key in M0 & M1 = M0 \ {key} &
;; M2 = ({d1} cup M3 cup M4) \ {key} & M3 < d1 < M4 & !(parent = nil) & d1 > key & ! cur2 = nil & keymin in M11 & keymin <= M11

(assert (not 
	(and
	(tobool 
	(ssep 
		(index alpha8 (bsthole root0 parent M1 M2) )
		(pto parent (sref (ref left keynode) (ref right Y) (ref data d1) ) ) 
		(pto keynode (sref (ref left X) (ref right rgt) (ref data key) ) ) 
		(index alpha9 (bst X M5) )
		(index alpha10 (bsthole rgt nxtparent2 M8 M10) )
		(pto nxtparent2 (sref (ref left cur2) (ref right U) (ref data d4) ) ) 
		(index alpha11 (bst cur2 M11) )
		(index alpha12 (bst U M12) )
		(index alpha13 (bst Y M4))		
	))
	(< M5 (bag key) )
	(< (bag key) (bagunion M8 (bag keymin)) )
	(= M10 (bagminus (bagunion (bag d4) M11 M12) (bag keymin) ) )
	(< M11 (bag d4) )
	(< (bag d4) M12)
	(= M3 (bagunion (bag key) M5 M8 (bag keymin)))
	(subset (bag key) M0)
	(= M1 (bagminus M0 (bag key)))
	(= M2 (bagminus (bagunion (bag d1) M3 M4) (bag key) ) )
	(< M3 (bag d1))
	(< (bag d1) M4)
	(distinct parent nil)
	(> d1 key)
	(distinct cur2 nil)
	(subset (bag keymin) M11)
	(<= (bag keymin) M11)
	)
))

(check-sat)
