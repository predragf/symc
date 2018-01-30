(declare-const R Real)
(declare-const PI Real)
(declare-const SLIP_ABS_ON Real)

(declare-const c1 Real)
(declare-const c2 Real)
(declare-const c3 Real)
(declare-const c4 Real)
(declare-const c5 Real)
(declare-const c6 Real)
(declare-const c7 Real)
(declare-const c8 Real)
(declare-const c9 Real)
(declare-const c10 Real)
(declare-const c11 Real)
(declare-const c12 Real)
(declare-const c13 Real)
(declare-const c14 Real)


(assert (= R 0.5))
(assert (= PI 3.14))
(assert (= SLIP_ABS_ON 0.1))

;(assert (< c2 PI))
;(assert (= c3 15))
;OR
;can there be c2 and c3 such that they do not fulfill the initial condition but the result is 0
(assert (not (> (* c5 0.9) c4)))

(assert (= c1 20))

(assert (= c5 (* (/ 10 36) c2)))
(assert (= c4 (* c3 (/ (* R PI) 30))))
(assert (= c6 (- c5 c4)))
(assert (= c6 c7))
(assert (= c8 (* 10 c7)))
(assert (= c9 (* (* 10 SLIP_ABS_ON) c5)))
(assert (ite (> c8 c9) (= c10 1.0) (= c10 0.0)))
(assert (= c11 0))
(assert (ite (> c10 0) (= c12 c11) (= c12 c1)))

(assert (= c10 1))
(assert (= c12 0))

(check-sat)
