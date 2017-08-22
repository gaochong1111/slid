(set-logic QF_SLRDI)

(declare-sort RBth_t 0)

(declare-fun left() (Field RBth_t RBth_t))
(declare-fun right() (Field RBth_t RBth_t))
(declare-fun data() (Field RBth_t Rat))
(declare-fun color() (Field RBth_t Rat))

(define-fun rbth ((?E RBth_t) (?x Rat) (?y Rat) (?z Rat) (?F RBth_t) (?x1 Rat) (?y1 Rat) (?z1 Rat)) Space
(tospace
    (or
        (and
            (= ?E ?F)
            (= ?x ?x1)
            (= ?y ?y1)
            (= ?z ?z1)
            (tobool emp)
        )

        (exists ((?X RBth_t) (?Y RBth_t) (?u Rat) (?x2 Rat) (?y2 Rat))
            (and
                (< ?y2 ?u)
                (< ?u ?x2)
                (<= ?z 2)
                (tobool
                    (ssep
                        (pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?u) (ref color ?z)))
                        (rbth ?X ?x ?y2 1 ?F ?x1 ?y1 ?z1)
                        (rbth ?Y ?x2 ?y 1 nil ?y ?y 1)
                    )
                )
            )
        )
    )
)
)

(declare-fun Z1() RBth_t)
(declare-fun Z2() RBth_t)
(declare-fun Z3() RBth_t)
(declare-fun Z4() RBth_t)

(declare-fun r1() Rat)
(declare-fun r2() Rat)
(declare-fun r3() Rat)
(declare-fun r4() Rat)
(declare-fun r5() Rat)

(declare-fun h1() Int)
(declare-fun h2() Int)


(assert (and true (distinct Z1 Z2) (< r1 r2) (= h1 h2) (<= h1 (+ h2 10)) (tobool (ssep (pto Z1 (sref (ref left Z2) (ref right Z3) (ref data r1) (ref color h1))) (rbth Z2 r2 r3 0 Z4 r4 r5 1)))))

(check-sat)


