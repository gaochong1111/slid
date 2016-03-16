
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
(declare-fun root0 () Bst_t)
(declare-fun cur1 () Bst_t)
(declare-fun cur2 () Bst_t)
(declare-fun parent () Bst_t)
(declare-fun keynode () Bst_t)
(declare-fun rgt () Bst_t)
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
(declare-fun M8 () BagInt)
(declare-fun M9 () BagInt)
(declare-fun M10 () BagInt)

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
(declare-fun alpha10 () SetLoc)
(declare-fun alpha11 () SetLoc)

;; VC16: bsthole(root0, parent, M1, M2) * parent |-> ((left,X), (right,cur1), (data, d1)) * bst(X, M3) * cur1 |-> ((left,Y), (right,U), (data, d2)) *
;; bst(Y, M5) * U |-> ((left,V), (right,Z), (data,d3)) * bst(V, M6) * bst(Z,M7) & M10 = {d3} cup M6 cup M7 & M6 < d3 < M7 &  
;; M4 = {d2} cup M5 cup M10 & M5 < d2 < M10 & M1 = M0 \ {key} & M2 = ({d1} cup M3 cup M4) \ {key} & M3 < d1 < M4 & !(parent = nil) & d1 < key & 
;; (key in M0 <=> key in M4) & keynode = cur1 & d2 = key & !U = nil & rgt = U & !V = nil & cur2 = V & nxtparent2 = rgt & M8 = M9 & 
;; M9 = M10 \ {keymin} & keymin in M6 & keymin <= M6|- 
;; bsthole(root0, parent, M1, M2) * parent |-> ((left, X), (right, keynode), (data, d1)) * bst(X,M3) * 
;; keynode |-> ((left,Y), (right, rgt), (data, key)) * bst(Y,M5) * bsthole(rgt, nxtparent2, M8, M9) * 
;; nxtparent2 |-> ((left, cur2), (right, Z), (data, d3)) * bst(cur2, M6) * bst(Z, M7) & 
;; M5 < key < M8 cup {keymin} & M9 = ({d3} cup M6 cup M7) \ {keymin} & M6 < d3 < M7 & M4 = {key} cup M5 cup M8 cup {keymin} & key in M0 & 
;; M1 = M0 \ {key} & M2 = ({d1} cup M3 cup M4) \ {key} & M3 < d1 < M4 & !(parent = nil) & d1 < key & ! cur2 = nil & keymin in M6 & keymin <= M6


(assert 
	(and
	(tobool 
	(ssep 
		(index alpha1 (bsthole root0 parent M1 M2))
		(pto parent (sref (ref left X) (ref right cur1) (ref data d1) ) ) 
		(index alpha2 (bst X M3) )
		(pto cur1 (sref (ref left Y) (ref right U) (ref data d2) ) ) 
		(index alpha3 (bst Y M5) )
		(pto U (sref (ref left V) (ref right Z) (ref data d3) ) ) 
		(index alpha4 (bst V M6) )
		(index alpha5 (bst Z M7) )
	))
	(= M10 (bag-union (singleton d3) (bag-union M6 M7) ) )
	(< M6 (singleton d3) )
	(< (singleton d3) M7)
	(= M4 (bag-union (singleton d2) (bag-union M5 M10) ) )
	(< M5 (singleton d2) )
	(< (singleton d2) M10 )
	(= M1 (bag-diff M0 (singleton key)) )
	(= M2 (bag-diff (bag-union (singleton d1) (bag-union M3 M4)) (singleton key)) )
	(< M3 (singleton d1) )
	(< (singleton d1) M4)
	(distinct parent nil)
	(< d1 key)
	(iff (bag-sub (singleton key) M0) (bag-sub (singleton key) M4) )
	(= keynode cur1)
	(= d2 key)
	(distinct U nil)
	(= rgt U)
	(distinct V nil)
	(= cur2 V)
	(= nxtparent2 rgt)
	(= M8 M9)
	(= M9 (bag-diff M10 (singleton keymin)))
	(bag-sub (singleton keymin) M6)
	(<= (singleton keymin) M6)
	)
)

;; bsthole(root0, parent, M1, M2) * parent |-> ((left, X), (right, keynode), (data, d1)) * bst(X,M3) * 
;; keynode |-> ((left,Y), (right, rgt), (data, key)) * bst(Y,M5) * bsthole(rgt, nxtparent2, M8, M9) * 
;; nxtparent2 |-> ((left, cur2), (right, Z), (data, d3)) * bst(cur2, M6) * bst(Z, M7) & 
;; M5 < key < M8 cup {keymin} & M9 = ({d3} cup M6 cup M7) \ {keymin} & M6 < d3 < M7 & M4 = {key} cup M5 cup M8 cup {keymin} & key in M0 & 
;; M1 = M0 \ {key} & M2 = ({d1} cup M3 cup M4) \ {key} & M3 < d1 < M4 & !(parent = nil) & d1 < key & ! cur2 = nil & keymin in M6 & keymin <= M6

(assert (not 
	(and
	(tobool 
	(ssep 
		(index alpha6 (bsthole root0 parent M1 M2) )
		(pto parent (sref (ref left X) (ref right keynode) (ref data d1) ) ) 
		(index alpha7 (bst X M3) )
		(pto keynode (sref (ref left Y) (ref right rgt) (ref data key) ) ) 
		(index alpha8 (bst Y M5) )
		(index alpha9 (bsthole rgt nxtparent2 M8 M9) )
		(pto nxtparent2 (sref (ref left cur2) (ref right Z) (ref data d3) ) ) 
		(index alpha10 (bst cur2 M6) )
		(index alpha11 (bst Z M7) )		
	))
	(< M5 (singleton key) )
	(< (singleton key) (bag-union M8 (singleton keymin)) )
	(= M9 (bag-diff (bag-union (singleton d3) (bag-union M6 M7) ) (singleton keymin) ) )
	(< M6 (singleton d3) )
	(< (singleton d3) M7)
	(= M4 (bag-union (singleton key) (bag-union M5 (bag-union M8 (singleton keymin)))))
	(bag-sub (singleton key) M0)
	(= M1 (bag-diff M0 (singleton key)))
	(= M2 (bag-diff (bag-union (singleton d1) (bag-union M3 M4) ) (singleton key) ) )
	(< M3 (singleton d1))
	(< (singleton d1) M4)
	(distinct parent nil)
	(< d1 key)
	(distinct cur2 nil)
	(bag-sub (singleton keymin) M6)
	(<= (singleton keymin) M6)
	)
))

(check-sat)
