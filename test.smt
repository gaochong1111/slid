(set-logic QF_SLRDI)

(declare-sort Sll_t 0)

(declare-fun next() (Field Sll_t Real))



(define-fun ls ((?E Sll_t) (?F Sll_t)) Space (tospace
            (or
            (and (= ?E ?F)
            (tobool emp))

            (exists ((?X Sll_t))
                (and (distinct ?E ?F)
                     (tobool (ssep (pto ?E (ref next ?X))
                     (ls ?X ?F)))
             ))
             )
))

(declare-fun X_temp () Real)

(check-sat)



