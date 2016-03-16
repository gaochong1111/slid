
; Extending QF_S:
; constant emptybag, 
; the function bag, 
; the multiset comparison operator bag-lt, bag-le, bag-gt, bag-ge
; bagunion, bag-diff, bag-sub

(set-logic QF_SLRDI)

;; declare sorts
(declare-sort Rbt_t 0)

;; declare fields
(declare-fun left () (Field Rbt_t Rbt_t))
(declare-fun right () (Field Rbt_t Rbt_t))
(declare-fun data () (Field Rbt_t Int))
(declare-fun color () (Field Rbt_t Int))

;; declare predicates

;; Each node has two data fields: data, color (0: red, 1: black). 
;; the rbt predicate defined here does not require the root to be black

;; rbt(E, M, N, C)::= E = nil & emp & M = emptyset & N = 1 & C = 1 | 
;; exists X,Y,M1,M2,N1,N2,C1,C2. E |-> ((left,X), (right,Y)) * rbt(X,M1,N1,C1) * rbt(Y,M2,N2,C2) & M = {E.data} cup M1 cup M2 & 
;; M1 < E.data < M2 & N1 = N2 & C = E.color  & 0 <= C <= 1 & ite(C=0, N = N1, N=N1+1) & C = 0 => (C1 = 1 & C2 = 1)


(define-fun rbt ((?E Rbt_t) (?M BagInt) (?N Int) (?C Int)) Space (tospace 
	(or 
	(and (= ?E nil) 
		(tobool emp
		)
		(= ?M emptybag)
		(= ?N 1)
		(= ?C 1)
	)
 
	(exists ( (?X Rbt_t) (?Y Rbt_t) (?M1 BagInt) (?M2 BagInt) (?N1 Int) (?N2 Int) (?C1 Int) (?C2 Int) (?d Int) (?c Int) ) 
	(and (distinct ?E nil) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref color ?c) ) ) 
			(rbt ?X ?M1 ?N1 ?C1)
			(rbt ?Y ?M2 ?N2 ?C2)
		)
		)
		(= ?M (bagunion ?M1 (bag ?d) ?M2) )
		(< ?M1 (bag ?d))
		(< (bag ?d) ?M2)
		(= ?N (ite (= ?C 0) ?N1 (+ ?N1 1) ) )
		(= ?N1 ?N2)
		(= ?c ?C)	
		(= ?C 0) (= ?C1 1) (= ?C2 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?M1 BagInt) (?M2 BagInt) (?N1 Int) (?N2 Int) (?C1 Int) (?C2 Int) (?d Int) (?c Int) ) 
	(and (distinct ?E nil) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref color ?c) ) ) 
			(rbt ?X ?M1 ?N1 ?C1)
			(rbt ?Y ?M2 ?N2 ?C2)
		)
		)
		(= ?M (bagunion ?M1 (bag ?d) ?M2) )
		(< ?M1 (bag ?d))
		(< (bag ?d) ?M2)
		(= ?N (ite (= ?C 0) ?N1 (+ ?N1 1) ) )
		(= ?N1 ?N2)
		(= ?c ?C)	
		(= ?C 1) (<= 0 ?C1) (<= ?C1 1) (<= 0 ?C2) (<= ?C2 1)
	)
	)
	)
))

;; rbthole(E,F, M1, N1, C1, M2, N2, C2)::= E = F & emp & M1 = M2 & N1 = N2 & C1 = C2 | 
;; exists X,Y,M3,M4,N3,N4, C3, C4. E |-> ((left,X), (right,Y)) * rbt(X,M3,N3,C3) * rbthole(Y,F,M4,N4,C4, M2, N2, C2) & 
;; M1 = {E.data} cup M3 cup M4 & M3 < E.data < M4 & N3 = N4 & C1 = E.color & 0 <= C1,C3,C4 <= 1 & ite(C1=0, N1=N3, N1=N3+1) & 
;; C1 = 0 => (C3 = 1 & C4 = 1) |
;; exists X,Y,M3,M4,N3,N4, C3, C4. E |-> ((left,X), (right,Y)) * rbthole(X,F,M3,N3,C3, M2, N2, C2) * rbt(Y,M4,N4,C4) & 
;; M1 = {E.data} cup M3 cup M4 & M3 < E.data < M4 & N3 = N4 & C1 = E.color & 0 <= C1,C3,C4 <= 1 & ite(C1=0, N1=N3, N2=N3+1) & 
;; C1 = 0 => (C3 = 1 & C4 = 1)

(define-fun rbthole ((?E Rbt_t) (?F Rbt_t) (?M1 BagInt) (?N1 Int) (?C1 Int) (?M2 BagInt) (?N2 Int) (?C2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?M1 ?M2)
		(= ?N1 ?N2)
		(= ?C1 ?C2)
	)
 
	(exists ( (?X Rbt_t) (?Y Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int) (?C4 Int) (?d Int) (?c Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref color ?c)) ) 
			(rbthole ?X ?F ?M3 ?N3 ?C3 ?M2 ?N2 ?C2)
			(rbt ?Y ?M4 ?N4 ?C4)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d) ?M4) )
		(< ?M3 (bag ?d))
		(< (bag ?d) ?M4)
		(= ?N1 (ite (= ?C1 0) ?N3 (+ ?N3 1) ) )
		(= ?N3 ?N4)
		(= ?c ?C1)	
		(= ?C1 0) (= ?C3 1) (= ?C4 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int) (?C4 Int) (?d Int) (?c Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref color ?c)) ) 
			(rbthole ?X ?F ?M3 ?N3 ?C3 ?M2 ?N2 ?C2)
			(rbt ?Y ?M4 ?N4 ?C4)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d) ?M4) )
		(< ?M3 (bag ?d))
		(< (bag ?d) ?M4)
		(= ?N1 (ite (= ?C1 0) ?N3 (+ ?N3 1) ) )
		(= ?N3 ?N4)
		(= ?c ?C1)	
		(= ?C1 1) (<= 0 ?C3) (<= ?C3 1) (<= 0 ?C4) (<= ?C4 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int) (?C4 Int) (?d Int) (?c Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref color ?c)) ) 
			(rbt ?X ?M3 ?N3 ?C3)
			(rbthole ?Y ?F ?M4 ?N4 ?C4 ?M2 ?N2 ?C2)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d) ?M4) )
		(< ?M3 (bag ?d))
		(< (bag ?d) ?M4)
		(= ?N1 (ite (= ?C1 0) ?N3 (+ ?N3 1) ) )
		(= ?N3 ?N4)
		(= ?c ?C1)	
		(= ?C1 0) (= ?C3 1)(= ?C4 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int) (?C4 Int) (?d Int) (?c Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d) (ref color ?c)) ) 
			(rbt ?X ?M3 ?N3 ?C3)
			(rbthole ?Y ?F ?M4 ?N4 ?C4 ?M2 ?N2 ?C2)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d) ?M4) )
		(< ?M3 (bag ?d))
		(< (bag ?d) ?M4)
		(= ?N1 (ite (= ?C1 0) ?N3 (+ ?N3 1) ) )
		(= ?N3 ?N4)
		(= ?c ?C1)	
		(= ?C1 1) (<= 0 ?C3) (<= ?C3 1) (<= 0 ?C4) (<= ?C4 1)
	)
	)
	)
))


;; rbthole with the property that the nodes on the path from E to F alternate between red and black, 
;; with the root black, and all the children of black nodes are red nodes

;; brrbthole(E,F, M1, N1, C1, M2, N2, C2)::= E = F & emp & M1 = M2 & N1 = N2 & C1 = C2 | 
;; exists X,Y,U,V,M3,M4,M5,N3,N4,N5,C3,C4,C5. E |-> ((left,X), (right,Y)) * Y |->((left,U),(right,V)) * rbt(X,M3,N3,C3) * 
;; brrbthole(U,F,M4,N4,C4,M2,N2,C2) * rbt(V,M5,N5,C5) & M1 = {E.data} cup M3 cup {Y.data} cup M4 cup M5 & 
;; M3 < E.data < {Y.data} cup M4 cup M5 & M4 < Y.data < M5 & C1 = E.color & C1 = 1 & C3 = 0 & Y.color = 0 & C4 = 1 & N4 = N5 & 
;; N3 = N4 & N1 = N3 +1 | 
;; exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * Y |->((left,U),(right,V)) * rbt(X,M3,N3,C3) * 
;; rbt(U,M4,N4,C4) * brrbthole(V,F,M5,N5,C5,M2,N2,C2) & M1 = {E.data} cup M3 cup {Y.data} cup M4 cup M5 & M3 < E.data < 
;; {Y.data} cup M4 cup M5 & M4 < Y.data < M5 & C1 = E.color & C1 = 1 & C3 = 0 & Y.color = 0 & C5 = 1 & N4 = N5 & N3 = N4 & N1 = N3 +1
;; | exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * X |->((left,U),(right,V)) * rbt(U,M3,N3,C3) * 
;; brrbthole(V,F,M4,N4,C4,M2,N2,C2) * rbt(Y,M5,N5,C5) & M1 = {E.data} cup {X.data} cup M3 cup M4 cup M5 & {X.data} cup M3 cup M4 <
;; E.data < M5 & M3 < X.data < M4 & C1 = E.color & C1 = 1 & X.color = 0 & C5 = 0 & C4 = 1 & N3 = N4 & N3 = N5 & N1 = N5 +1 |
;; exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * X |->((left,U),(right,V)) * 
;; brrbthole(U,F,M3,N3,C3, M2, N2, C2) * rbt(V,M4,N4,C4) * rbt(Y,M5,N5,C5) & M1 = {E.data} cup {X.data} cup M3 cup M4 cup M5 &
;; {X.data} cup M3 cup M4 < E.data < M5 & M3 < X.data < M4 & C1 = E.color & C1 = 1 & X.color = 0 & C5 = 0 & C3 = 1 & N3 = N4 & 
;; N3 = N5 & N1 = N5 +1

(define-fun brrbthole ((?E Rbt_t) (?F Rbt_t) (?M1 BagInt) (?N1 Int) (?C1 Int) (?M2 BagInt) (?N2 Int) (?C2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?M1 ?M2)
		(= ?N1 ?N2)
		(= ?C1 ?C2)
	)
 
	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int) (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?d2 Int) (?c1 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(pto ?X (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(brrbthole ?U ?F ?M3 ?N3 ?C3 ?M2 ?N2 ?C2)
			(rbt ?V ?M4 ?N4 ?C4) 
			(rbt ?Y ?M5 ?N5 ?C5)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d2) ?M4 (bag ?d1) ?M5) )
		(< ?M3 (bag ?d2)) (< (bag ?d2) ?M4)
		(< (bagunion ?M3 (bag ?d2) ?M4) (bag ?d1)) (< (bag ?d1) ?M5) 
		(= ?N1 (+ ?N5 1))
		(= ?N3 ?N4) (= ?N3 ?N5) 
		(= ?C1 1) (= ?C3 1) (= ?C4 1) (= ?C5 0) (= ?c1 1) (= ?c2 0)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int)  (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?c1 Int) (?d2 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(pto ?X (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(rbt ?U ?M3 ?N3 ?C3) 
			(brrbthole ?V ?F ?M4 ?N4 ?C4 ?M2 ?N2 ?C2)
			(rbt ?Y ?M5 ?N5 ?C5)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d2) ?M4 (bag ?d1) ?M5) )
		(< ?M3 (bag ?d2)) (< (bag ?d2) ?M4)
		(< (bagunion ?M3 (bag ?d2) ?M4) (bag ?d1)) (< (bag ?d1) ?M5) 
		(= ?N1 (+ ?N5 1))
		(= ?N3 ?N4) (= ?N3 ?N5)
		(= ?C1 1)  (= ?C3 1) (= ?C4 1) (= ?C5 0) (= ?c1 1) (= ?c2 0)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int)  (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?c1 Int) (?d2 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(rbt ?X ?M3 ?N3 ?C3)
			(pto ?Y (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(brrbthole ?U ?F ?M4 ?N4 ?C4 ?M2 ?N2 ?C2)
			(rbt ?V ?M5 ?N5 ?C5) 
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d1) ?M4 (bag ?d2) ?M5 ) )
		(< ?M4 (bag ?d2)) (< (bag ?d2) ?M5)
		(< ?M3 (bag ?d1)) (< (bag ?d1) (bagunion ?M4 (bag ?d2) ?M5))  
		(= ?N1 (+ ?N3 1))
		(= ?N4 ?N5) (= ?N3 ?N5)
		(= ?C1 1)  (= ?C3 0) (= ?C4 1) (= ?C5 1) (= ?c1 1) (= ?c2 0)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int)  (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?c1 Int) (?d2 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(rbt ?X ?M3 ?N3 ?C3)
			(pto ?Y (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(rbt ?U ?M4 ?N4 ?C4) 
			(brrbthole ?V ?F ?M5 ?N5 ?C5 ?M2 ?N2 ?C2)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d1) ?M4 (bag ?d2) ?M5 ) )
		(< ?M4 (bag ?d2)) (< (bag ?d2) ?M5)
		(< ?M3 (bag ?d1)) (< (bag ?d1) (bagunion ?M4 (bag ?d2) ?M5))  
		(= ?N1 (+ ?N3 1))
		(= ?N4 ?N5) (= ?N3 ?N4)
		(= ?C1 1)  (= ?C3 0) (= ?C4 1) (= ?C5 1) (= ?c1 1) (= ?c2 0)
	)
	)
	)
))


;; the dual predicate of brrbthole, with red and black exchanged

;; rbrbthole(E,F, M1, N1, C1, M2, N2, C2)::= E = F & emp & M1 = M2 & H1 = H2 & C1 = C2 | 
;; exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * Y |->((left,U),(right,V)) * rbt(X,M3,N3,C3) * 
;; rbrbthole(U,F,M4,N4,C4,M2,N2,C2) * rbt(V,M5,N5,C5) & M1 = {E.data} cup M3 cup {Y.data} cup M4 cup M5 & M3 < E.data < 
;; {Y.data} cup M4 cup M5 & M4 < Y.data < M5 & C1 = E.color & C1 = 0 & C3 = 1 & Y.color = 1 & C4 = 0 & N4 = N5 & N3 = N4 + 1 & 
;; N1 = N3 |
;; exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * Y |->((left,U),(right,V)) * rbt(X,M3,N3,C3) * 
;; rbt(U,M4,N4,C4) * rbrbthole(V,F,M5,N5,C5,M2,N2,C2) & M1 = {E.data} cup M3 cup {Y.data} cup M4 cup M5 & M3 < E.data < 
;; {Y.data} cup M4 cup M5 & M4 < Y.data < M5 & C1 = E.color & C1 = 0 & C3 = 1 & Y.color = 1 & C5 = 0 & N4 = N5 & N3 = N4 + 1 & 
;; N1 = N3 |
;; exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * X |->((left,U),(right,V)) * rbt(U,M3,N3,C3) * 
;; rbrbthole(V,F,M4,N4,C4,M2,N2,C2) * rbt(Y,M5,N5,C5) & M1 = {E.data} cup {X.data} cup M3 cup M4 cup M5 & {X.data} cup M3 cup M4 <
;; E.data < M5 & M3 < X.data < M4 & C1 = E.color & C1 = 0 & X.color = 1 & C5 = 1 & C4 = 0 & N3 = N4 & N5 = N3+1 & N1 = N5 |
;; exists X,Y,U,V,M3,M4,M5,H3,H4,H5,C3,C4,C5. E |-> ((left,X), (right,Y)) * X |->((left,U),(right,V)) * 
;; rbrbthole(U,F,M3,N3,C3, M2, N2, C2) * rbt(V,M4,N4,C4) * rbt(Y,M5,N5,C5) & M1 = {E.data} cup {X.data} cup M3 cup M4 cup M5 &
;; {X.data} cup M3 cup M4 < E.data < M5 & M3 < X.data < M4 & C1 = E.color & C1 = 0 & X.color = 1 & C5 = 1 & C3 = 0 & N3 = N4 & 
;; N5 = N3+1 & N1 = N5


(define-fun rbrbthole ((?E Rbt_t) (?F Rbt_t) (?M1 BagInt) (?N1 Int) (?C1 Int) (?M2 BagInt) (?N2 Int) (?C2 Int)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?M1 ?M2)
		(= ?N1 ?N2)
		(= ?C1 ?C2)
	)
 
	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int) (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?d2 Int) (?c1 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(pto ?X (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(rbrbthole ?U ?F ?M3 ?N3 ?C3 ?M2 ?N2 ?C2)
			(rbt ?V ?M4 ?N4 ?C4) 
			(rbt ?Y ?M5 ?N5 ?C5)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d2) ?M4 (bag ?d1) ?M5) )
		(< ?M3 (bag ?d2)) (< (bag ?d2) ?M4)
		(< (bagunion ?M3 (bag ?d2) ?M4) (bag ?d1)) (< (bag ?d1) ?M5) 
		(= ?N1 (+ ?N5 1))
		(= ?N3 ?N4) (= ?N3 ?N5) 
		(= ?C1 0) (= ?C3 0) (= ?C4 0) (= ?C5 1) (= ?c1 0) (= ?c2 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int)  (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?c1 Int) (?d2 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(pto ?X (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(rbt ?U ?M3 ?N3 ?C3) 
			(rbrbthole ?V ?F ?M4 ?N4 ?C4 ?M2 ?N2 ?C2)
			(rbt ?Y ?M5 ?N5 ?C5)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d2) ?M4 (bag ?d1) ?M5) )
		(< ?M3 (bag ?d2)) (< (bag ?d2) ?M4)
		(< (bagunion ?M3 (bag ?d2) ?M4) (bag ?d1)) (< (bag ?d1) ?M5) 
		(= ?N1 (+ ?N5 1))
		(= ?N3 ?N4) (= ?N3 ?N5)
		(= ?C1 0)  (= ?C3 0) (= ?C4 0) (= ?C5 1) (= ?c1 0) (= ?c2 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int)  (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?c1 Int) (?d2 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(rbt ?X ?M3 ?N3 ?C3)
			(pto ?Y (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(rbrbthole ?U ?F ?M4 ?N4 ?C4 ?M2 ?N2 ?C2)
			(rbt ?V ?M5 ?N5 ?C5) 
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d1) ?M4 (bag ?d2) ?M5 ) )
		(< ?M4 (bag ?d2)) (< (bag ?d2) ?M5)
		(< ?M3 (bag ?d1)) (< (bag ?d1) (bagunion ?M4 (bag ?d2) ?M5))  
		(= ?N1 (+ ?N3 1))
		(= ?N4 ?N5) (= ?N3 ?N5)
		(= ?C1 0)  (= ?C3 1) (= ?C4 0) (= ?C5 0) (= ?c1 0) (= ?c2 1)
	)
	)

	(exists ( (?X Rbt_t) (?Y Rbt_t) (?U Rbt_t) (?V Rbt_t) (?M3 BagInt) (?N3 Int) (?C3 Int) (?M4 BagInt) (?N4 Int)  (?C4 Int)
		(?M5 BagInt) (?N5 Int) (?C5 Int) (?d1 Int) (?c1 Int) (?d2 Int) (?c2 Int) ) 
	(and (distinct ?E ?F) 
		(tobool 
		(ssep 
			(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d1) (ref color ?c1)) ) 
			(rbt ?X ?M3 ?N3 ?C3)
			(pto ?Y (sref (ref left ?U) (ref right ?V) (ref data ?d2) (ref color ?c2)) )
			(rbt ?U ?M4 ?N4 ?C4) 
			(rbrbthole ?V ?F ?M5 ?N5 ?C5 ?M2 ?N2 ?C2)
		)
		)
		(= ?M1 (bagunion ?M3 (bag ?d1) ?M4 (bag ?d2) ?M5 ) )
		(< ?M4 (bag ?d2)) (< (bag ?d2) ?M5)
		(< ?M3 (bag ?d1)) (< (bag ?d1) (bagunion ?M4 (bag ?d2) ?M5))  
		(= ?N1 (+ ?N3 1))
		(= ?N4 ?N5) (= ?N3 ?N4)
		(= ?C1 0)  (= ?C3 1) (= ?C4 0) (= ?C5 0) (= ?c1 0) (= ?c2 1)
	)
	)
	)
))

;; declare variables
(declare-fun root () Rbt_t)
(declare-fun root0 () Rbt_t)
(declare-fun cur () Rbt_t)
(declare-fun cur1 () Rbt_t)
(declare-fun cur2 () Rbt_t)
(declare-fun parent () Rbt_t)
(declare-fun parent0 () Rbt_t)
(declare-fun parent1 () Rbt_t)
(declare-fun parent2 () Rbt_t)
(declare-fun uncle () Rbt_t)
(declare-fun uncle1 () Rbt_t)
(declare-fun uncle2 () Rbt_t)
(declare-fun grandpa () Rbt_t)
(declare-fun grandpa1 () Rbt_t)
(declare-fun grandpa2 () Rbt_t)
(declare-fun ggrandpa () Rbt_t)
(declare-fun ggrandpa1 () Rbt_t)
(declare-fun ggrandpa2 () Rbt_t)
(declare-fun cusparent1 () Rbt_t)
(declare-fun cusparent2 () Rbt_t)
(declare-fun cusnode1 () Rbt_t)
(declare-fun cusnode2 () Rbt_t)
(declare-fun cu () Rbt_t)
(declare-fun cu1 () Rbt_t)
(declare-fun cu2 () Rbt_t)
(declare-fun pa () Rbt_t)
(declare-fun gra () Rbt_t)
(declare-fun ret () Rbt_t)

(declare-fun x () Rbt_t)
(declare-fun X () Rbt_t)
(declare-fun Y () Rbt_t)
(declare-fun Z () Rbt_t)
(declare-fun U () Rbt_t)
(declare-fun V () Rbt_t)
(declare-fun W () Rbt_t)
(declare-fun U1 () Rbt_t)
(declare-fun V1 () Rbt_t)
(declare-fun U2 () Rbt_t)
(declare-fun V2 () Rbt_t)

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
(declare-fun M17 () BagInt)

(declare-fun N1 () Int)
(declare-fun N2 () Int)
(declare-fun N3 () Int)
(declare-fun N4 () Int)
(declare-fun N5 () Int)
(declare-fun N6 () Int)
(declare-fun N7 () Int)
(declare-fun N8 () Int)
(declare-fun N9 () Int)
(declare-fun N10 () Int)
(declare-fun N11 () Int)
(declare-fun N12 () Int)
(declare-fun N13 () Int)
(declare-fun N14 () Int)
(declare-fun N15 () Int)
(declare-fun N16 () Int)
(declare-fun N17 () Int)

(declare-fun n1 () Int)
(declare-fun n2 () Int)
(declare-fun n3 () Int)
(declare-fun n4 () Int)
(declare-fun n5 () Int)
(declare-fun n6 () Int)
(declare-fun n7 () Int)
(declare-fun n8 () Int)
(declare-fun n9 () Int)
(declare-fun n10 () Int)
(declare-fun iseven () Int)

(declare-fun C1 () Int)
(declare-fun C2 () Int)
(declare-fun C3 () Int)
(declare-fun C4 () Int)
(declare-fun C5 () Int)
(declare-fun C6 () Int)
(declare-fun C7 () Int)
(declare-fun C8 () Int)
(declare-fun C9 () Int)
(declare-fun C10 () Int)
(declare-fun C11 () Int)
(declare-fun C12 () Int)
(declare-fun C13 () Int)
(declare-fun C14 () Int)
(declare-fun C15 () Int)
(declare-fun C16 () Int)
(declare-fun C17 () Int)

(declare-fun d1 () Int)
(declare-fun d2 () Int)
(declare-fun d3 () Int)
(declare-fun d4 () Int)
(declare-fun d5 () Int)
(declare-fun d6 () Int)
(declare-fun d7 () Int)
(declare-fun d8 () Int)
(declare-fun d9 () Int)
(declare-fun cz () Int)
(declare-fun c1 () Int)
(declare-fun c2 () Int)
(declare-fun c3 () Int)
(declare-fun c4 () Int)
(declare-fun c5 () Int)
(declare-fun c6 () Int)
(declare-fun c7 () Int)
(declare-fun c8 () Int)

(declare-fun key () Int)

;; declare set of locations

(declare-fun alpha0 () SetLoc)
(declare-fun alpha00 () SetLoc)
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
(declare-fun alpha14 () SetLoc)
(declare-fun alpha15 () SetLoc)
(declare-fun alpha16 () SetLoc)
(declare-fun alpha17 () SetLoc)
(declare-fun alpha18 () SetLoc)


;; VC11:
;; rbthole(root,cusparent1,M1,N1,C1,M2,N2,C2) * cusparent1 |-> ((left,cusnode1),(right,X),(data,d1),(color,c1)) * rbt(X,M3,N3,C3) * 
;; cusnode1 |-> ((left, ggrandpa1),(right,Y),(data,d2),(color,c2)) * rbt(Y,M4,N4,C4) * ggrandpa1 |-> ((left,grandpa1),(right,U),
;; (data,d3),(color,c3)) * rbt(U,M5,N5,C5) * grandpa1 |-> ((left,parent0),(right,uncle1),(data,d4),(color,c4)) * rbt(uncle1,M6,N6,C6) 
;; * parent0 |-> ((left,x),(right,Z),(data,d5),(color,c5)) * x |-> ((left,nil),(right,nil),(data,key),(color,0)) * rbt(Z,M7,N7,C7)
;; & key < d5 < M7 & N7=1 & 0<=c5<=1 & c5=0 => C7 = 1 & {key} cup {d5} cup M7 < d4 < M6 & n5=ite(c5=0, N7,N7+1) & n5 = N6 & 
;; 0<= c4 <= 1 & (c4=0 => c5 =1 & C6 = 1) & {key} cup {d5} cup M7 cup {d4} cup M6 < d3 < M5 & n4=ite(c4=0,N6,N6+1) & n4=N5 & 
;; 0 <=c3 <= 1 & (c3 =0 => c4 =1 & C5 = 1) & {key} cup {d5} cup M7 cup {d4} cup M6 cup {d3} cup M5 < d2 < M4 & n3=ite(c3=0,N5,N5+1) &
;; n3=N4 & 0 <=c2 <= 1 & (c2 =0 => c3 =1 & C4 = 1) & {key} cup {d5} cup M7 cup {d4} cup M6 cup {d3} cup M5 cup {d2} cup M4 < d1 < M3 &
;; n2=ite(c2=0,N4,N4+1) & n2=N3 & 0 <=c1 <= 1 & (c1 =0 => c2 =1 & C3 = 1) & M2 = {key} cup {d5} cup M7 cup {d4} cup M6 cup {d3} cup M5
;; cup {d2} cup M4 cup {d1} cup M3 & N2 = ite(c1=0,N3,N3+1) & C2= c1 & M0 cup {key} = M1 & ! key in M0 & ! parent0 = nil & 
;; ! parent0 = root & ! cusparent1 = nil & is_even = 1 & c5 =0 & C6 = 0 parent1 = parent0 & cur1 = x & ggrandpa2 = grandpa1 & 
;; grandpa2 = parent1 & uncle2 = Z & parent2 = cur1 & cur2 = nil
;; |-
;; rbthole(root,cusparent2,M1,N1,C1,M2,N2,C2) * cusparent2 |-> ((left,cusnode2),(right,X),(data,d1),(color,c1)) * rbt(X,M3,N3,C3) * 
;; cusnode2 |-> ((left, ggrandpa1),(right,Y),(data,d2),(color,c2)) * rbt(Y,M4,N4,C4) * ggrandpa1 |-> ((left, ggrandpa2),(right,U),
;; (data,d3),(color,c3)) * rbt(U,M5,N5,C5) * brrbthole(ggrandpa2,x,M8,N8,C8,M9,N9,C9) * x |-> ((left,nil),(right,nil),(data,key),
;; (color,0)) * rbt(Z,M7,N7,C7)
;; & key < d5 < M7 & N7=1 & 0<=c5<=1 & c5=0 => C7 = 1 &  M9 = {key} & N9 = 1 & C9=0 & M8 < d3 < M5 & N8=N5 & 0 <=c3 <= 1 & 
;; (c3 =0 => C8 =1 & C5 = 1) & M8 cup {d3} cup M5 < d2 < M4 & n3=ite(c3=0,N5,N5+1) & n3=N4 & 0 <=c2 <= 1 & (c2 =0 => c3 =1 & C4 = 1) &
;; M8 cup {d3} cup M5 cup {d2} cup M4 < d1 < M3 & n2=ite(c2=0,N4,N4+1) & n2=N3 & 0 <=c1 <= 1 & (c1 =0 => c2 =1 & C3 = 1) & 
;; M2 = M8 cup {d3} cup M5 cup {d2} cup M4 cup {d1} cup M3 & N2 = ite(c1=0,N3,N3+1) & C2= c1 & M0 cup {key} = M1 & ! key in M0 & 
;; ! parent0 = nil & ! parent0 = root & ! cusparent1 = nil & is_even = 0 & grandpa2 = parent0 & parent2 = x & cur2 = nil & uncle2 = Z


(assert 
	(and
	(tobool 
	(ssep 
		(index alpha1 (rbthole root cusparent1 M1 N1 C1 M2 N2 C2))
		(pto cusparent1 (sref (ref left cusnode1) (ref right X) (ref data d1) (ref color c1)))
		(index alpha2 (rbt X M3 N3 C3))
		(pto cusnode1 (sref (ref left ggrandpa1) (ref right Y) (ref data d2) (ref color c2)))
		(index alpha3 (rbt Y M4 N4 C4)) 
		(pto ggrandpa1 (sref (ref left grandpa1) (ref right U) (ref data d3) (ref color c3)))
		(index alpha4 (rbt U M5 N5 C5))
		(pto grandpa1 (sref (ref left parent0) (ref right uncle1) (ref data d4) (ref color c4)))
		(index alpha5 (rbt uncle1 M6 N6 C6))
		(pto parent0 (sref (ref left x) (ref right Z) (ref data d5) (ref color c5)))
		(pto x (sref (ref left nil) (ref right nil) (ref data key) (ref color c6)))
		(index alpha6 (rbt Z M7 N7 C7))
	))
	(< key d5) (< (bag d5) M7) (= N7 1) (<= 0 c5) (<= c5 1) (=> (= c5 0) (= C7 1))
	(< (bagunion (bag key) (bag d5) M7) (bag d4)) (< (bag d4) M6) 
	(= N6 (ite (= c5 0) N7 (+ N7 1)) ) (<= 0 c4) (<= c4 1) (=> (= c4 0) (= c5 1) ) (=> (= c4 0) (= C6 1) ) 
	(< (bagunion (bag key) (bag d5) M7 (bag d4) M6) (bag d3) ) (< (bag d3) M5) 
	(= N5  (ite (= c4 0) N6 (+ N6 1)) ) (<= 0 c3) (<= c3 1) (=> (= c3 0) (= c4 1) ) (=> (= c3 0) (= C5 1) ) 
	(< (bagunion (bag key) (bag d5) M7 (bag d4) M6 (bag d3) M5) (bag d2)) (< (bag d2) M4)
	(= N4 (ite (= c3 0) N5 (+ N5 1)) ) (<= 0 c2) (<= c2 1) (=> (= c2 0) (= c3 1) ) (=> (= c2 0) (= C4 1) ) 
	(< (bagunion (bag key) (bag d5) M7 (bag d4) M6 (bag d3) M5 (bag d2) M4) (bag d1)) (< (bag d1) M3)
	(= N3 (ite (= c2 0) N4 (+ N4 1)) ) (<= 0 c1) (<= c1 1)
	(=> (= c1 0) (= c2 1) ) (=> (= c1 0) (= C3 1) ) 
	(= M2 (bagunion (bag key) (bag d5) M7 (bag d4) M6 (bag d3) M5 (bag d2) M4 (bag d1) M3) )
	(= N2 (ite (= c1 0) N3 (+ N3 1)) ) (= C2 c1) (= (bagunion M0 (bag key)) M1)
	(= M0 (bagminus M0 (bag key)) ) (distinct parent0 nil) (distinct parent0 root) (distinct cusparent1 nil)
	(= iseven 1) (= c5 0) (= C6 0) (= parent1 parent0) (= cur1 x) 
	(= ggrandpa2 grandpa1) (= cusparent2 cusparent1) (= cusnode2 cusnode1)
	(= grandpa2 parent1) (= uncle2 Z) (= parent2 cur1) (= cur2 nil) (= c6 0)
	)
)

;; rbthole(root,cusparent2,M1,N1,C1,M2,N2,C2) * cusparent2 |-> ((left,cusnode2),(right,X),(data,d1),(color,c1)) * rbt(X,M3,N3,C3) *
;; cusnode2 |-> ((left, ggrandpa1),(right,Y),(data,d2),(color,c2)) * rbt(Y,M4,N4,C4) * ggrandpa1 |-> ((left, ggrandpa2),(right,U),
;; (data,d3),(color,c3)) * rbt(U,M5,N5,C5) * brrbthole(ggrandpa2,x,M8,N8,C8,M9,N9,C9) * x |-> ((left,nil),(right,nil),(data,key),
;; (color,0))
;; & key < d5 < M7 & N7=1 & 0<=c5<=1 & c5=0 => C7 = 1 &  M9 = {key} & N9 = 1 & C9=0 & M8 < d3 < M5 & N8=N5 & 0 <=c3 <= 1 & 
;; (c3 =0 => C8 =1 & C5 = 1) & M8 cup {d3} cup M5 < d2 < M4 & n3=ite(c3=0,N5,N5+1) & n3=N4 & 0 <=c2 <= 1 & (c2 =0 => c3 =1 & C4 = 1) &
;; M8 cup {d3} cup M5 cup {d2} cup M4 < d1 < M3 & n2=ite(c2=0,N4,N4+1) & n2=N3 & 0 <=c1 <= 1 & (c1 =0 => c2 =1 & C3 = 1) & 
;; M2 = M8 cup {d3} cup M5 cup {d2} cup M4 cup {d1} cup M3 & N2 = ite(c1=0,N3,N3+1) & C2= c1 & M0 cup {key} = M1 & ! key in M0 & 
;; ! parent0 = nil & ! parent0 = root & ! cusparent1 = nil & is_even = 0 & grandpa2 = parent0 & parent2 = x & cur2 = nil & uncle2 = Z

(assert (not 
	(and 
	(tobool 
	(ssep 
		(index alpha7 (rbthole root cusparent2 M1 N1 C1 M2 N2 C2))
		(pto cusparent2 (sref (ref left cusnode2) (ref right X) (ref data d1) (ref color c1)))
		(index alpha8 (rbt X M3 N3 C3))
		(pto cusnode2 (sref (ref left ggrandpa1) (ref right Y) (ref data d2) (ref color c2)))
		(index alpha9 (rbt Y M4 N4 C4)) 
		(pto ggrandpa1 (sref (ref left ggrandpa2) (ref right U) (ref data d3) (ref color c3)))
		(index alpha10 (rbt U M5 N5 C5)) 
		(index alpha11 (brrbthole ggrandpa2 x M8 N8 C8 M9 N9 C9))
		(pto x (sref (ref left nil) (ref right nil) (ref data key) (ref color c6)))
	))
	(< key d5) (< (bag d5) M7) (= N7 1) (<= 0 c5) (<= c5 1) (=> (= c5 0) (= C7 1) ) 
	(= M9 (bag key)) (= N9 1) (= C9 0) (< M8 (bag d3)) (< (bag d3) M5) (= N8 N5) (<= 0 c3) (<= c3 1)
	(=> (= c3 0) (= C8 1) ) (=> (= c3 0) (= C5 1) ) (< (bagunion M8 (bag d3) M5) (bag d2)) (< (bag d2) M4)
	(= N4 (ite (= c3 0) N5 (+ N5 1)) ) (<= 0 c2) (<= c2 1) (=> (= c2 0) (= c3 1) ) (=> (= c2 0) (= C4 1) ) 
	(< (bagunion M8 (bag d3) M5 (bag d2) M4) (bag d1)) (< (bag d1) M3)
	(= N3  (ite (= c2 0) N4 (+ N4 1)) ) (<= 0 c1) (<= c1 1)
	(=> (= c1 0) (= c2 1) ) (=> (= c1 0) (= C3 1) ) (= M2 (bagunion M8 (bag d3) M5 (bag d2) M4  (bag d1) M3) )
	(= N2 (ite (= c1 0) N3 (+ N3 1)) ) (= C2 c1) (= M1 (bagunion M0 (bag key)) )
	(= M0 (bagminus M0 (bag key)) ) (distinct parent0 nil) (distinct parent0 root) (distinct cusparent1 nil)
	(= iseven 1) (= grandpa2 parent0) (= parent2 x) (= cur2 nil) (= uncle2 Z) (= c6 0)
	)
))

(check-sat)
