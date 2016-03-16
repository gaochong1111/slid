
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
(declare-fun root () Bst_t)
(declare-fun cur () Bst_t)
(declare-fun parent () Bst_t)
(declare-fun ret () Bst_t)
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
(declare-fun key () Int)
(declare-fun d1 () Int)
(declare-fun d2 () Int)

;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)
(declare-fun alpha5 () SetLoc)


;;VC10: bsthole(root,parent, M1, M2) * parent|->((left,X), (right, cur), (data, d1)) * bst(X,M3) * cur |- ((left, Y), (right, Z), (data,d2)) * bst(Y, M5) * bst(Z, M6) & M4 = {d2} cup M5 cup M6 & M5 < d2 < M6 & M3 < d1 < M4 & ite(key in M0, M1 = M0, M1 = M0 cup {key}) & ite(key in M4, M2 = {d1} cup M3 cup M4, M2 = {d1} cup M3 cup M4 cup {key}) & key in M0 <=> key in M4 & d1 < key & ! parent = nil & ! cur = nil & d2 = key & ret = root |- key in M0 & bst(ret, M0) & ret = root

(assert 
	(and
	(tobool 
	(ssep 
		(index alpha1 (bsthole root parent M1 M2) )
		(pto parent (sref (ref left X) (ref right cur) (ref data d1) ) ) 
		(index alpha2 (bst X M3) )
		(pto cur (sref (ref left Y) (ref right Z) (ref data d2) ) ) 
		(index alpha3 (bst Y M5) )
		(index alpha4 (bst Z M6) )
	))
	(= M4 (bagunion (bag d2) M5 M6) )
	(< M5 (bag d2) )
	(< (bag d2) M6)
	(< M3 (bag d1) )
	(< (bag d1) M4)
	(= M1 (ite (subset (bag key) M0) M0 (bagunion M0 (bag key)) ) ) 
	(= M2 (ite (subset (bag key) M4) (bagunion (bag d1) M3 M4) 
			                 (bagunion (bag d1) M3 M4 (bag key) ) ) )
	(=> (subset (bag key) M0) (subset (bag key) M4) )
	(=> (subset (bag key) M4) (subset (bag key) M0) )
	(< d1 key)
	(distinct parent nil)
	(distinct cur nil)
	(= d2 key)
	(= ret root)
	)
)

(assert (not 
	(and 
	(tobool 
		(index alpha5 (bst ret M0) )
	)
	(subset (bag key) M0)
	(= ret root)
	)
))

(check-sat)
