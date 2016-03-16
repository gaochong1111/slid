(set-logic QF_S)

(declare-sort Sll_t 0)
(declare-sort Bll_t 0)

(declare-fun next1 () (Field Sll_t Sll_t))
(declare-fun next2 () (Field Sll_t Sll_t))
(declare-fun next3 () (Field Sll_t Bll_t))

; singly-linked list
(define-fun lstb ((?in Sll_t) (?out Sll_t) (?brd Bll_t))
  Space (tospace (or (= ?in ?out) 
    (exists ((?u Sll_t)) 
    (and (distinct ?in ?out) (distinct ?in ?brd)
    (tobool (ssep
      (pto ?in (sref
				(ref next1 ?u)
				(ref next2 ?u)
				(ref next3 ?brd)))
      (lstb ?u ?out ?brd))
))))))

(declare-fun x_emp () Sll_t)
(declare-fun y_emp () Sll_t)
(declare-fun z_emp () Sll_t)
(declare-fun w_emp () Bll_t)
(declare-fun alpha1 () SetLoc)
(assert
  (and (distinct x_emp z_emp) (distinct y_emp z_emp) (distinct x_emp w_emp) (distinct y_emp w_emp)
  (tobool (ssep 
      (pto x_emp (sref (ref next1 y_emp) (ref next2 y_emp) (ref next3 w_emp)))
      (pto y_emp (sref (ref next1 z_emp) (ref next2 z_emp) (ref next3 w_emp)))
))))

(assert
  (not
    (tobool (index alpha1 (lstb x_emp z_emp w_emp)))
))

(check-sat)
