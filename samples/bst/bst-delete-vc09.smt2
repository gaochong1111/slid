
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
(declare-fun parent () Bst_t)
(declare-fun X () Bst_t)
(declare-fun Y () Bst_t)
(declare-fun Z () Bst_t)
(declare-fun lft () Bst_t)
(declare-fun subroot () Bst_t)
(declare-fun keynode () Bst_t)
(declare-fun M0 () BagInt)
(declare-fun M1 () BagInt)
(declare-fun M2 () BagInt)
(declare-fun M3 () BagInt)
(declare-fun M4 () BagInt)
(declare-fun M5 () BagInt)
(declare-fun M6 () BagInt)
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

;; VC09: bsthole(root0, parent, M1, M2) * parent |-> ((left,cur), (right,Y), (data, d1)) * bst(X, M5) * bst(Z,M6) * bst(Y,M4) & 
;; M3 = {d2} cup M5 cup M6 & M5 < d2 < M6 & M1 = M0 \ {key} & M2 = ({d1} cup M3 cup M4) \ {key} & M3 < d1 < M4 & !(parent = nil) & 
;; d1 > key & (key in M0 <=> key in M3) & d2 = key & keynode = cur & ! keynode = nil & Z = nil & lft = X & subroot = lft |-
;; bsthole(root0, parent, M1, M2) * parent |-> ((left, keynode), (right,Y), (data, d1)) * bst(subroot, M5) * bst(Y,M4) & 
;; M1 = M0 \ {key} & M5 = M3 \ {key} & M2 = {d1} cup M5 cup M4 & M5 < d1 < M4 & d1 > key & key in M3 & key in M0 & !(parent = nil)

(assert 
	(and
	(tobool 
	(ssep 
		(index alpha1 (bsthole root0 parent M1 M2) )
		(pto parent (sref (ref left cur) (ref right Y) (ref data d1) ) )
		(index alpha2 (bst X M5) )
		(index alpha3 (bst Z M6) )
		(index alpha4 (bst Y M4) )
	))
	(= M3 (bag-union (singleton d2) (bag-union M5 M6) ) )
	(< M5 (singleton d2) )
	(< (singleton d2) M6 )
	(= M1 (bag-diff M0 (singleton key)) )
	(= M2 (bag-diff (bag-union (singleton d1) (bag-union M3 M4)) (singleton key) ) )
	(< M3 (singleton d1) )
	(< (singleton d1) M4 )
	(distinct parent nil)
	(> d1 key)
	(iff (bag-sub (singleton key) M0) (bag-sub (singleton key) M3) )
	(= d2 key)
	(= keynode cur)
	(distinct keynode nil)
	(= Z nil)
	(= lft X)
	(= subroot lft)
	)
)

;; bsthole(root0, parent, M1, M2) * parent |-> ((left, keynode), (right,Y), (data, d1)) * bst(subroot, M5) * bst(Y,M4) & 
;; M1 = M0 \ {key} & M5 = M3 \ {key} & M2 = {d1} cup M5 cup M4 & M5 < d1 < M4 & d1 > key & key in M3 & key in M0 & !(parent = nil)

(assert (not 
	(and
	(tobool 
	(ssep 
		(index alpha5 (bsthole root0 parent M1 M2))
		(pto parent (sref (ref left keynode) (ref right Y) (ref data d1)) )
		(index alpha6 (bst subroot M5))
		(index alpha7 (bst Y M4))
	))
	(= M1 (bag-diff M0 (singleton key)) )
	(= M5 (bag-diff M3 (singleton key)) )
	(= M2 (bag-union (singleton d1) (bag-union M5 M4)))
	(< M5 (singleton d1))
	(< (singleton d1) M4)
	(> d1 key)
	(bag-sub (singleton key) M3)
	(bag-sub (singleton key) M0)
	(distinct parent nil)
	)
))

(check-sat)
