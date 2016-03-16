
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
(declare-fun parent1 () Avl_t)
(declare-fun parent2 () Avl_t)
(declare-fun unbalance1 () Avl_t)
(declare-fun unbalance2 () Avl_t)
(declare-fun unbparent1 () Avl_t)
(declare-fun unbparent2 () Avl_t)
(declare-fun X () Avl_t)
(declare-fun Y () Avl_t)
(declare-fun Z () Avl_t)
(declare-fun U () Avl_t)
(declare-fun V () Avl_t)
(declare-fun W () Avl_t)

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

(declare-fun H1 () Int)
(declare-fun H2 () Int)
(declare-fun H3 () Int)
(declare-fun H4 () Int)
(declare-fun H5 () Int)
(declare-fun H6 () Int)
(declare-fun H7 () Int)
(declare-fun H8 () Int)
(declare-fun H9 () Int)
(declare-fun H10 () Int)
(declare-fun H11 () Int)
(declare-fun h () Int)

(declare-fun d1 () Int)
(declare-fun d2 () Int)
(declare-fun d3 () Int)
(declare-fun d4 () Int)
(declare-fun b1 () Int)
(declare-fun b2 () Int)
(declare-fun b3 () Int)
(declare-fun b4 () Int)
(declare-fun key () Int)

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

;; VC04: avlhole(root, unbparent1, M1,H1,M2,H2) * unbparent1 |-> ((left,unbalance1),(right,X),(data,d1),(balance,b1)) * 
;; unbalance1 |-> ((left,Y),(right,Z),(data,d2),(balance,b2)) * bavlhole(Y,parent1,M4,H4,M6,H6) * parent1 |-> ((left,cur1),(right,U),(data,d3),
;; (balance,b3)) * cur1 |-> ((left,W),(right,V),(data,d4),(balance,b4)) * avl(W, M10, H10) * avl(V,M11,H11) * avl(U,M8,H8) * avl(Z, M5,H5) * 
;; avl(X, M3, H3) & M7 = {d4} cup M10 cup M11 & M10 < d4 < M11 & ite(H11 > H10, H7 = H11+1,H7=H10+1) & b4 = H11-H10 & -1 <=b4<=1 & M7 < d3 < M8 & 
;; b3 = H8 - H7 & -1 <= b3 <= 1 & ite(key in M7, M6 = {d3} cup M7 cup M8, M6 = {d3} cup M7 cup M8 cup {key}) & ite(H8>H7, H6 = H8+1, H6 = H7+1) & 
;; M4 < d2 < M5 & b2 = H5 - H4 & ite(key in M0, M2 = {d1} cup {d2} cup M4 cup M5 cup M3, M2 = {d1} cup {d2} cup M4 cup M5 cup M3 cup {key}) & 
;; {d2} cup M4 cup M5 < d1 < M3 & ite(H5>H4, h = H5 +1, h= H4 +1) & b1 = H3 - h  & -1<= b1 <= 1 & ite(key in M0, M1 = M0, M1 = M0 cup {key}) & 
;; key in M0 <=> key in M7 & ! parent1 = nil & ! unbparent1 = nil & d1> key & d2 > key & d3 > key & ! b2 = 0 & !b4=0 & unbalance2 = cur1 & 
;; unbparent2 = parent1 & !cur1 = nil & parent2 = cur1 & d4 > key & cur2 = W & ite(key in M10, M9 = {d3} cup M7 cup M8, M9 = {d3} cup M7 cup 
;; M8 cup {key}) & H9 = H6 |-
;; avlhole(root, unbparent2, M1,H1,M9,H9) * unbparent2 |-> ((left,unbalance2),(right,U),(data,d3),(balance,b3)) * 
;; parent2 |-> ((left,cur2),(right,V),(data,d4),(balance,b4)) * avl(cur2, M10, H10) * avl(V,M11,H11) * avl(U, M8,H8) & M10 < d4 < M11 & 
;; b4 = H11 - H10 & -1 <= b4 <= 1 & ite(key in M10, M9 = {d3} cup {d4} cup M10 cup M11 cup M8, M9 = {d3} cup {d4} cup M10 cup M11 cup M8 cup {key}) &
;; ite(H11 > H10, H7=H11+1, H7=H10+1) & ite(H8 > H7, H9 = H8+1, H9 = H7+1) & {d4} cup M10 cup M11 < d3 < M8 & b3 = H8 - H7 & -1<= b3 <= 1 & 
;; ite(key in M0, M1 = M0, M1 = M0 cup {key}) & key in M0 <=> key in M10 & ! parent2 = nil & ! unbparent2 = nil & unbalance2 = parent2 & 
;; d3 > key & d4 > key & ! b4 = 0

(assert 
	(and
	(tobool 
	(ssep 
		(index alpha1 (avlhole root unbparent1 M1 H1 M2 H2))
		(pto unbparent1  (sref (ref left unbalance1) (ref right X) (ref data d1) (ref balance b1) ))
		(pto unbalance1 (sref (ref left Y) (ref right Z) (ref data d2) (ref balance b2) ) ) 
		(index alpha2 (bavlhole Y parent1 M4 H4 M6 H6) ) 
		(pto parent1 (sref (ref left cur1) (ref right U) (ref data d3) (ref balance b3)) )
		(pto cur1  (sref (ref left W) (ref right V) (ref data d4) (ref balance b4)) )
		(index alpha3 (avl W M10 H10))
		(index alpha4 (avl V M11 H11))
		(index alpha5 (avl U M8 H8))
		(index alpha6 (avl Z M5 H5))
		(index alpha7 (avl X M3 H3))
	))
	(= M7 (bagunion (bag d4) M10 M11) ) (< M10 (bag d4)) (< (bag d4) M11) 
	(= H7 (ite (> H11 H10) (+ H11 1) (+ H10 1)) ) (= b4  (- H11 H10))
	(<= (- 0 1) b4) (<= b4 1) (< M7 (bag d3)) (< (bag d3) M8) (= b3 (- H8 H7) ) (<= (- 0 1) b3) (<= b3 1) 
	(= M6 (ite (subset (bag key) M7) (bagunion (bag d3)  M7 M8) (bagunion (bag d3) M7 M8 (bag key)) ) ) 
	(= H6 (ite (> H8 H7) (+ H8 1) (+ H7 1)) )	
	(< M4 (bag d2))(< (bag d2) M5) (= b2 (- H5 H4)) 
	(= M2 (ite (subset (bag key) M0) (bagunion (bag d1) (bag d2) M4 M5 M3) (bagunion (bag d1) (bag d2) M4 M5 M3 (bag key)) ) )
	(< (bagunion (bag d2) M4 M5) (bag d1)) (< (bag d1) M3) 
	(= h (ite (> H5 H4) (+ H5 1) (+ H4 1)) )
	(= b1 (- H3 h)) (<= (- 0 1) b1) (<= b1 1) (= M1 (ite (subset (bag key) M0) M0 (bagunion M0 (bag key)) ) )
	(=> (subset (bag key) M0) (subset (bag key) M7) ) 
	(=> (subset (bag key) M7) (subset (bag key) M0) ) 
	(distinct parent1 nil) (distinct unbparent1 nil)
	(> d1 key) (> d2 key) (> d3 key) (distinct b2 0) (distinct b4 0) (= unbalance2 cur1)
	(= unbparent2 parent1) (distinct cur1 nil) (= parent2 cur1) (> d4 key) (= cur2 W) 
	(= M9 (ite (subset (bag key) M10) (bagunion (bag d3) M7 M8) (bagunion (bag d3) M7 M8 (bag key)) ) ) 
	(= H9 H6)
	)
)

;; avlhole(root, unbparent2, M1,H1,M9,H9) * unbparent2 |-> ((left,unbalance2),(right,U),(data,d3),(balance,b3)) * 
;; parent2 |-> ((left,cur2),(right,V),(data,d4),(balance,b4)) * avl(cur2, M10, H10) * avl(V,M11,H11) * avl(U, M8,H8) & M10 < d4 < M11 & 
;; b4 = H11 - H10 & -1 <= b4 <= 1 & ite(key in M10, M9 = {d3} cup {d4} cup M10 cup M11 cup M8, M9 = {d3} cup {d4} cup M10 cup M11 cup M8 cup {key}) &
;; ite(H11 > H10, H7=H11+1, H7=H10+1) & ite(H8 > H7, H9 = H8+1, H9 = H7+1) & {d4} cup M10 cup M11 < d3 < M8 & b3 = H8 - H7 & -1<= b3 <= 1 & 
;; ite(key in M0, M1 = M0, M1 = M0 cup {key}) & key in M0 <=> key in M10 & ! parent2 = nil & ! unbparent2 = nil & unbalance2 = parent2 & 
;; d3 > key & d4 > key & ! b4 = 0

(assert (not 
	(and 
	(tobool 
	(ssep 
		(index alpha8 (avlhole root unbparent2 M1 H1 M9 H9))
		(pto unbparent2 (sref (ref left unbalance2) (ref right U) (ref data d3) (ref balance b3)))	
		(pto parent2 (sref (ref left cur2) (ref right V) (ref data d4) (ref balance b4)))
		(index alpha9 (avl cur2 M10 H10))
		(index alpha10 (avl V M11 H11))
		(index alpha11 (avl U M8 H8))
	))
	(< M10 (bag d4)) (< (bag d4) M11)
	(= b4  (- H11 H10)) (<= (- 0 1) b4) (<= b4 1)
	(= M9 (ite (subset (bag key) M10) (bagunion (bag d3) (bag d4) M10 M11 M8) (bagunion (bag d3) (bag d4) M10 M11 M8 (bag key)) ) )
	(= H7 (ite (> H11 H10) (+ H11 1) (+ H10 1) ) ) 
	(= H9 (ite (> H8 H7) (+ H8 1) (+ H7 1)) )
	(< (bagunion (bag d4) M10 M11) (bag d3))(< (bag d3) M8)
	(= b3 (- H8 H7)) (<= (- 0 1) b3) (<= b3 1)	
	(= M1 (ite (subset (bag key) M0) M0 (bagunion M0 (bag key)) ) ) 
	(=> (subset (bag key) M0) (subset (bag key) M10) ) 
	(=> (subset (bag key) M10) (subset (bag key) M0) ) 
	(distinct parent2  nil) (distinct unbparent2 nil) (= unbalance2 parent2) (> d3 key) (> d4 key) (distinct b4 0)
	)
))

(check-sat)
