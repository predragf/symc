(define-fun LOOKUP ((x Real)) Real
  (ite (= x 0.0) 0.0 (ite (and (> x 0) (< x 20)) (/ (* x 147) 2) (ite (= x 20) 1470 (ite (and (> x 20) (< x 30)) (- 1470 (* 49 (- x 20))) 980)))))

(define-fun-rec R ((a Real) (b Real) (min Int) (max Int)) Real
    (ite (= min max) (+ 1 max) (ite (> max min) (ite (< a (* b (/ (+ min max) 2))) (R a b min (to_int (/ (+ min max) 2))) (ite (> a (* b (+ 1 (/ (+ min max) 2)))) (R a b (+ (to_int (/ (+ min max) 2)) 1) max) (ite (<= (* b (- a (/ (+ min max) 2))) (- (* b (+ 1 (/ (+ min max) 2))) a)) (/ (+ min max) 2) (+ 1 (/ (+ min max) 2))))) 20)))

(define-fun BSR ((m Real) (g Real)) Real (ite (or (= m 0) (= g 0)) 0 (ite (> m (* 100 g)) 100 (R m g 0 99))))

(declare-const maxbraketorque Real)
(declare-const distrib Real)
(declare-const r Real)
(declare-const _pi Real)
(declare-const slip_abs_on Real)
(declare-const t_veh Real)

(declare-const use_division Real)
(declare-const w_max Real)
(declare-const m Real)
(declare-const v_max Real)
(declare-const w0 Real)
(declare-const i Real)
(declare-const v0 Real)

(assert (! (=  v0 0) :named init1))
(assert (! (=  maxbraketorque 3000):named init2))
(assert (! (=  distrib 3) :named init3))
(assert (! (=  r 0.5) :named init4))
(assert (! (=  _pi 3.14) :named init5))
(assert (! (=  slip_abs_on 0.1) :named init6))
(assert (! (=  t_veh 0.005) :named init7))

(assert (! (=  use_division 0) :named init8))
(assert (! (=  w_max 112) :named init9))
(assert (! (=  m 2000) :named init10))
(assert (! (=  v_max 56) :named init11))
(assert (! (=  w0 (/ v0 r)) :named init12))
(assert (! (=  i (/ (* m (* r r)))) :named init13))
