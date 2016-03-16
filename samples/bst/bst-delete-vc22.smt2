
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
(declare-fun cur () Bst_t)
(declare-fun rgt () Bst_t)
(declare-fun parent () Bst_t)
(declare-fun keynode () Bst_t)
(declare-fun subroot () Bst_t)
(declare-fun nxtparent () Bst_t)
(declare-fun X () Bst_t)
(declare-fun Y () Bst_t)
(declare-fun Z () Bst_t)
(declare-fun U () Bst_t)
(declare-fun V () Bst_t)
(declare-fun W () Bst_t)

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
(declare-fun M13 () BagInt)
(declare-fun M14 () BagInt)
(declare-fun M15 () BagInt)
(declare-fun M16 () BagInt)

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

;; VC22: bsthole(root0, parent, M1, M2) * parent |-> ((left, X), (right, keynode), (data, d1)) * bst(Y,M5) * 
;; bsthole(rgt, nxtparent, M8, M10) * nxtparent |-> ((left, W), (right, U), (data, d2)) * 
;; cur |->((left,Y),(right,rgt), (data,d3)) * bst(V,M15) * bst(W,M16) * bst(Z, M12) & M11 = {d3} cup M15 cup M16 & 
;; M15 < d3 < M16 & M5 < key < M8 cup {keymin} & M10 = ({d2} cup M11 cup M12) \ {keymin} & M11 < d2 < M12 & 
;; M4 = {key} cup M5 cup M8 cup {keymin} & key in M0 & M1 = M0 \ {key} & M2 = ({d1} cup M3 cup M4) \ {key} & 
;; M3 < d1 < M4 & !(parent = nil) & d1 < key & ! cur = nil & keymin in M11 & keymin <= M11 & V = nil & subroot = cur & 
;; M14 = {d3} cup M5 cup M8 |-
;; bsthole(root0, parent, M1, M2) * parent |-> ((left, X), (right,keynode), (data, d1)) * bst(X,M3) * bst(subroot, M14) &
;; M14 = M4 \ {key} & M2 = {d1} cup M3 cup M14 & M3 < d1 < M4 & d1 < key & key in M4 & key in M0 & M1 = M0 \ {key} & 
;; ! parent = nil

(assert 
	(and
	(tobool 
	(ssep 
		(index alpha1 (bsthole root0 parent M1 M2) )
		(pto parent (sref (ref left X) (ref right keynode) (ref data d1) ) )
		(index alpha2 (bst Y M5)) 
		(index alpha3 (bsthole rgt nxtparent M8 M10)) 
		(pto nxtparent (sref (ref left W) (ref right U) (ref data d2) ) )
		(pto cur (sref (ref left Y) (ref right rgt) (ref data d3) ) )
		(index alpha4 (bst V M15) )
		(index alpha5 (bst W M16) )
		(index alpha6 (bst Z M12) )
	))
	(= M11 (bag-union (singleton d3) (bag-union M15 M16))
	(< M15 (singleton d3) )
	(< (singleton d3) M16)
	(< M5 (singleton d3) )
	(< (singleton d3) (bag-union M8 (singleton keymin)) )
	(= M10 (bag-diff (bag-union (singleton d2) (bag-union M11 M12)) (singleton keymin)) )
	(< M11 (singleton d2) )
	(< (singleton d2) M12)
	(< M3 (singleton d1) )
	(< (singleton d1) M4)
	(distinct parent nil)
	(< d1 key)
	(distinct cur nil)
	(bag-sub (singleton keymin) M11)
	(<= (singleton keymin) M11)
	(= V nil)
	(= subroot cur)
	(= M14 (bag-union (singleton d3) (bag-union M5 M8)) )
	)
)

;; bsthole(root0, parent, M1, M2) * parent |-> ((left, X), (right,keynode), (data, d1)) * bst(X,M3) * bst(subroot, M14) &
;; M14 = M4 \ {key} & M2 = {d1} cup M3 cup M14 & M3 < d1 < M4 & d1 < key & key in M4 & key in M0 & M1 = M0 \ {key} & 
;; ! parent = nil

(assert (not 
	(and
	(tobool 
	(ssep 
		(index alpha7 (bsthole root0 parent M1 M2))
		(pto parent (sref (ref left X) (ref right keynode) (ref data d1)))
		(index alpha8 (bst X M13) )
		(index alpha9 (bst subroot M14) )		
	)
	)
	(= M14 (bag-diff M4 (singleton key)) )
	(= M2 (bag-union (singleton d1) (bag-union M3 M14)) )
	(< M3 (singleton d1))
	(< (singleton d1) M4)
	(< d1 key)
	(bag-sub (singleton key) M4)
	(bag-sub (singleton key) M0)
	(= M1 (bag-diff M0 (singleton key)) )
	(distinct parent nil)
	)
))

(check-sat)
