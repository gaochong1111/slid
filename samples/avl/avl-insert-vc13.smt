
; Extending QF_S:
; constant emptybag, 
; the function bag, 
; the multiset comparison operator bag-lt, bag-le, bag-gt, bag-ge
; bagunion, bag-diff, bag-sub

(set-logic QF_SLRDI)

;; declare sorts
(declare-sort Avl_t 0)

;; declare fields
(declare-fun left () (Field Avl_t Avl_t))
(declare-fun right () (Field Avl_t Avl_t))
(declare-fun data () (Field Avl_t Int))
(declare-fun balance () (Field Avl_t Int))

;; declare predicates

;; avl(E,M, H)::= E = nil & emp & M = emptyset & H = 0 | 
;; exists X,Y,M1,M2,H1,H2. !E=nil & E |-> ((left,X), (right,Y)) * avl(X,M1,H1) * avl(Y,M2,H2) & M = {E.data} cup M1 cup M2 & 
;; M1 < E.data < M2 & ite(H2 > H1, H = H2+1 , H = H1+1) & E.balance = H2 - H1 & -1 <= E.balance <= 1

(define-fun avl ((?E Avl_t) (?M BagInt) (?H Int)) Space (tospace 
	(or 
	(and 	(= ?E nil) 
		(tobool emp
		)
		(= ?M emptybag)
		(= ?H 0)
	)
 
	(exists ( (?X Avl_t) (?Y Avl_t) (?M1 BagInt) (?M2 BagInt) (?H1 Int) (?H2 Int) (?d Int) (?b Int) ) 
	(and 
		(distinct ?E nil) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref balance ?b)) ) 
			(avl ?X ?M1 ?H1)
			(avl ?Y ?M2 ?H2)
		)
		)
		(= ?M (bagunion (bag ?d) ?M1  ?M2) )
		(< ?M1 (bag ?d))
		(< (bag ?d) ?M2)
		(= ?H (ite (> ?H2 ?H1) (+ ?H2 1 ) (+ ?H1 1 ) ) )
		(= ?b (- ?H2 ?H1) )
		(<= (- 0 1) ?b) (<= ?b 1 )
	)
	)
	)
))

;; avlhole(E,F, M1, H1, M2, H2)::= E = F & emp & M1 = M2 & H1 = H2 | 
;; exists X,Y,M3,M4,H3,H4. E |-> ((left,X), (right,Y)) * avl(X,M3,H3) * avlhole(Y,F,M4,H4,M2,H2) & M1 = {E.data} cup M3 cup M4 & 
;; M3 < E.data < M4 & ite(H4 > H3, H1 = H4+1 , H = H3+1) & E.balance = H4 - H3 & -1 <= E.balance <= 1 |
;; exists X,Y,M3,M4,H3,H4. E |-> ((left,X), (right,Y)) * avlhole(X,F,M3,H3,M2,H2) * avl(Y,M4,H4) & M1 = {E.data} cup M3 cup M4 & 
;; M3 < E.data < M4 & ite(H4 > H3, H1 = H4+1 , H1 = H3+1) & E.balance = H4 - H3 & -1 <= E.balance <= 1

(define-fun avlhole ((?E Avl_t) (?F Avl_t) (?M1 BagInt) (?H1 Int) (?M2 BagInt) (?H2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?M1 ?M2)
		(= ?H1 ?H2)
	)
 
	(exists ( (?X Avl_t) (?Y Avl_t) (?M3 BagInt) (?M4 BagInt) (?H3 Int) (?H4 Int) (?d Int) (?b Int) ) 
	(and 
		(distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref balance ?b)) ) 
			(avlhole ?X ?F ?M3 ?H3 ?M2 ?H2)
			(avl ?Y ?M4 ?H4)
		)
		)
		(= ?M1 (bagunion (bag ?d) ?M3 ?M4) )
		(< ?M3 (bag ?d))
		(< (bag ?d) ?M4)
		(= ?H1 (ite (> ?H4 ?H3) (+ ?H4 1 ) (+ ?H3 1 ) ) )
		(= ?b (- ?H4 ?H3))
		(<= (- 0 1)  ?b) (<= ?b 1 )
	)
	)

	(exists ( (?X Avl_t) (?Y Avl_t) (?M3 BagInt) (?M4 BagInt) (?H3 Int) (?H4 Int) (?d Int) (?b Int) ) 
	(and 
		(distinct ?E ?F) 
		(tobool (ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref balance ?b)) ) 
			(avl ?X ?M3 ?H3)
			(avlhole ?Y ?F ?M4 ?H4 ?M2 ?H2)
		)
		)
		(= ?M1 (bagunion (bag ?d) ?M3 ?M4 ) )
		(< ?M3 (bag ?d))
		(< (bag ?d) ?M4)
		(= ?H1 (ite (> ?H4 ?H3) (+ ?H4 1 ) (+ ?H3 1 ) ) )
		(= ?b (- ?H4 ?H3) )
		(<= (- 0 1)  ?b) (<= ?b 1 )
	)
	)
	)
))



;; avlhole with the property that each node on the path from E to F is balanced

;; bavlhole(E,F, M1, H1, M2, H2)::= E = F & emp & M1 = M2 & H1 = H2 | 
;; exists X,Y,M3,M4,H3,H4. E |-> ((left,X), (right,Y)) * avl(X,M3,H3) * bavlhole(Y,F,M4,H4,M2,H2) & M1 = {E.data} cup M3 cup M4 & M3 < E.data < M4 
;; & H3 = H4 & H1 = H3+1 & E.balance = 0 |
;; exists X,Y,M3,M4,H3,H4. E |-> ((left,X), (right,Y)) * bavlhole(X,F,M3,H3,M2,H2) * avl(Y,M4,H4) & M1 = {E.data} cup M3 cup M4 & M3 < E.data < M4 
;; & H3 = H4 & H1 = H3+1 & E.balance = 0

(define-fun bavlhole ((?E Avl_t) (?F Avl_t) (?M1 BagInt) (?H1 Int) (?M2 BagInt) (?H2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?M1 ?M2)
		(= ?H1 ?H2)
	)
 
	(exists ( (?X Avl_t) (?Y Avl_t) (?M3 BagInt) (?M4 BagInt) (?H3 Int) (?H4 Int) (?d Int) (?b Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref balance ?b)) ) 
			(bavlhole ?X ?F ?M3 ?H3 ?M2 ?H2)
			(avl ?Y ?M4 ?H4)
		)
		)
		(= ?M1 (bagunion (bag ?d) ?M3 ?M4) )
		(< ?M3 (bag ?d))
		(< (bag ?d) ?M4)
		(= ?H1 (ite (> ?H4 ?H3) (+ ?H4 1 ) (+ ?H3 1 )) )
		(= ?b (- ?H4 ?H3))
		(= ?b 0)
	)
	)

	(exists ( (?X Avl_t) (?Y Avl_t) (?M3 BagInt) (?M4 BagInt) (?H3 Int) (?H4 Int) (?d Int) (?b Int) ) 
	(and (distinct ?E ?F) 
		(tobool (ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref balance ?b)) ) 
			(avl ?X ?M3 ?H3)
			(bavlhole ?Y ?F ?M4 ?H4 ?M2 ?H2)
		)
		)
		(= ?M1 (bagunion (bag ?d) ?M3 ?M4) )
		(< ?M3 (bag ?d) )
		(< (bag ?d) ?M4 )
		(= ?H4 (ite (> ?H4 ?H3) (+ ?H4 1 ) (+ ?H3 1 )) )
		(= ?b (- ?H4 ?H3) )
		(= ?b 0)
	)
	)

	)
))

;; avlhole with the property that each node on the path from E to F is unbalanced

;; ubavlhole(E,F, M1, H1, M2, H2)::= E = F & emp & M1 = M2 & H1 = H2 | 
;; exists X,Y,M3,M4,H3,H4. E |-> ((left,X), (right,Y)) * avl(X,M3,H3) * ubavlhole(Y,F,M4,H4,M2,H2) & M1 = {E.data} cup M3 cup M4 & 
;; M3 < E.data < M4 & H3 = H4 & H1 = H3+1 & -1 <= E.balance <=1 & ! E.balance = 0 |
;; exists X,Y,M3,M4,H3,H4. E |-> ((left,X), (right,Y)) * ubavlhole(X,F,M3,H3,M2,H2) * avl(Y,M4,H4) & M1 = {E.data} cup M3 cup M4 & 
;; M3 < E.data < M4 & H3 = H4 & H1 = H3+1 & -1 <= E.balance <=1 & ! E.balance = 0

(define-fun ubavlhole ((?E Avl_t) (?F Avl_t) (?M1 BagInt) (?H1 Int) (?M2 BagInt) (?H2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?M1 ?M2)
		(= ?H1 ?H2)
	)
 
	(exists ( (?X Avl_t) (?Y Avl_t) (?M3 BagInt) (?M4 BagInt) (?H3 Int) (?H4 Int) (?d Int) (?b Int) ) 
	(and (distinct ?E ?F) 
		(tobool (ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref balance ?b)) ) 
			(ubavlhole ?X ?F ?M3 ?H3 ?M2 ?H2)
			(avl ?Y ?M4 ?H4)
		)
		)
		(= ?M1 (bagunion (bag ?d) ?M3 ?M4 ) )
		(< ?M3 (bag ?d))
		(< (bag ?d) ?M4)
		(= ?H1 (ite (> ?H4 ?H3) (+ ?H4 1 ) (+ ?H3 1 ) ) )
		(= ?b (- ?H4 ?H3) )
		(<= (-  0 1 ) ?b) (<= ?b 1 )
		(distinct ?b 0)
	)
	)

	(exists ( (?X Avl_t) (?Y Avl_t) (?M3 BagInt) (?M4 BagInt) (?H3 Int) (?H4 Int) (?d Int) (?b Int) ) 
	(and (distinct ?E ?F) 
		(tobool (ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref balance ?b)) ) 
			(avl ?X ?M3 ?H3)
			(ubavlhole ?Y ?F ?M4 ?H4 ?M2 ?H2)
		)
		)
		(= ?M1 (bagunion (bag ?d) ?M3 ?M4 ) )
		(< ?M3 (bag ?d))
		(< (bag ?d) ?M4)
		(= ?H1 (ite (> ?H4 ?H3) (+ ?H4 1 ) (+ ?H3 1 )) )
		(= ?b (- ?H4 ?H3))
		(<= (-  0 1 ) ?b) (<= ?b 1 )
		(distinct ?b 0)
	)
	)

	)
))


;; declare variables
(declare-fun root () Avl_t)
(declare-fun cur1 () Avl_t)
(declare-fun cur2 () Avl_t)
(declare-fun parent () Avl_t)
(declare-fun unbalance () Avl_t)
(declare-fun unbparent () Avl_t)
(declare-fun x () Avl_t)
(declare-fun Y () Avl_t)

(declare-fun M0 () BagInt)
(declare-fun M2 () BagInt)

(declare-fun H1 () Int)
(declare-fun H2 () Int)

(declare-fun d1 () Int)
(declare-fun b1 () Int)
(declare-fun b2 () Int)
(declare-fun b3 () Int)
(declare-fun key () Int)

;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)


;; VC13: root |-> ((left,x),(right,Y),(data,d1),(balance,b2)) * x |->((left,nil),(right,nil),(data,key),(balance,0)) * avl(Y,M2,H2) & d1 < M2 & 
;; b1 = H2 & -1 <= b1 <= 1 & M0 = {d1} cup M2 & parent = root & unbparent = nil & unbalance = root & d1 > key & !key in M0 & cur1 = unbalance & 
;; b2 = b1 -1 & cur2 = x |-
;; root |-> ((left,x),(right,Y),(data,d1),(balance,b2)) * x |->((left,nil),(right,nil),(data,key),(balance,0)) * avl(Y,M2,H2) & d1 < M2 & 
;; b2 = H2-1 & M0 = {d1} cup M2 & parent = root & unbparent = nil & unbalance = root & d1 > key & !key in M0 & cur2 = x
 
(assert 
	(and
	(tobool 
	(ssep 
		(pto root (sref (ref left x) (ref right Y) (ref data d1) (ref balance b2)))
		(pto x (sref (ref left nil) (ref right nil) (ref data key) (ref balance b3)))
		(index alpha1 (avl Y M2 H2))
	))
	(< (bag d1) M2) (= b1 H2) (<= (- 0 1) b1) (<= b1 1) (=  M0 (bagunion (bag d1) M2)) 
	(= parent root) (= unbparent nil) (= unbalance root) (> d1 key) (= M0 (bagminus M0 (bag key)) )
	(= cur1 unbalance) (= b2 (- b1 1)) (= cur2 x) (= b3 0)
	)
)

;; root |-> ((left,x),(right,Y),(data,d1),(balance,b2)) * x |->((left,nil),(right,nil),(data,key),(balance,0)) * avl(Y,M2,H2) & d1 < M2 & 
;; b2 = H2-1 & M0 = {d1} cup M2 & parent = root & unbparent = nil & unbalance = root & d1 > key & !key in M0 & cur2 = x

(assert (not 
	(and 
	(tobool 
	(ssep 
		(pto root (sref (ref left x) (ref right Y) (ref data d1) (ref balance b2)))
		(pto x (sref (ref left nil) (ref right nil) (ref data key) (ref balance b3)))
		(index alpha3 (avl Y M2 H2))
	))
	(< (bag d1) M2)  (= b2 (- H2 1)) (= M0 (bagunion (bag d1) M2) )
	(= parent root) (= unbparent nil) (= unbalance root)  (> d1 key) (= M0 (bagminus M0 (bag key)) ) (= cur2 x) (= b3 0)
	)
))

(check-sat)
