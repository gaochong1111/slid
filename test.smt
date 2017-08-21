(set-logic QF_SLRDI)

(declare-sort Bsth_t 0)

(declare-fun left() (Field Bsth_t Bsth_t))
(declare-fun right() (Field Bsth_t Bsth_t))
(declare-fun data() (Field Bsth_t Rat))

(define-fun bsth ((?E Bsth_t) (?x Rat) (?y Rat) (?F Bsth_t) (?x1 Rat) (?y1 Rat)) Space
(tospace
    (or
        (and
            (= ?E ?F)
            (= ?x ?x1)
            (= ?y ?y1)
            (tobool emp)
        )

        (exists ((?X Bsth_t) (?Y Bsth_t) (?z Rat) (?x2 Rat) (?y2 Rat))
            (and
                (< ?y2 ?z)
                (< ?z ?x2)
                (tobool
                    (ssep
                        (pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?z)))
                        (bsth ?X ?x ?y2 ?F ?x1 ?y1)
                        (bsth ?Y ?x2 ?y nil ?y ?y)
                    )
                )
            )
        )

        (exists ((?X Bsth_t) (?Y Bsth_t) (?z Rat) (?x2 Rat) (?y2 Rat))
            (and
                (< ?y2 ?z)
                (< ?z ?x2)
                (tobool
                    (ssep
                        (pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?z)))
                        (bsth ?X ?x ?y2 nil ?x ?x)
                        (bsth ?Y ?x2 ?y ?F ?x1 ?y1)
                    )
                )
            )
        )
    )
)
)

(declare-fun Z1() Bsth_t)
(declare-fun Z2() Bsth_t)
(declare-fun Z3() Bsth_t)
(declare-fun Z4() Bsth_t)

(declare-fun r1() Rat)
(declare-fun r2() Rat)
(declare-fun r3() Rat)
(declare-fun r4() Rat)
(declare-fun r5() Rat)

(declare-fun h1() Int)
(declare-fun h2() Int)


(assert (and true (distinct Z1 Z2) (< r1 r2) (= h1 h2) (<= h1 (+ h2 10)) (tobool (ssep (pto Z1 (sref (ref left Z2) (ref right Z3) (ref data r1))) (bsth Z2 r2 r3 Z4 r4 r5)))))

(check-sat)



