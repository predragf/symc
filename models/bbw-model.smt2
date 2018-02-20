 
 (set-option :smt.mbqi true)

(define-fun LOOKUP ((x Real)) Real
  (ite (= x 0.0) 0.0 (ite (and (> x 0) (< x 20)) (/ (* x 147) 2) (ite (= x 20) 1470 (ite (and (> x 20) (< x 30)) (- 1470 (* 49 (- x 20))) 980)))))

(define-fun-rec RECURSION ((a Real) (b Real) (min Int) (max Int)) Real
    (ite (= min max) (+ 1 max) (ite (> max min) (ite (< a (* b (/ (+ min max) 2))) (RECURSION a b min (to_int (/ (+ min max) 2))) (ite (> a (* b (+ 1 (/ (+ min max) 2)))) (RECURSION a b (+ (to_int (/ (+ min max) 2)) 1) max) (ite (<= (* b (- a (/ (+ min max) 2))) (- (* b (+ 1 (/ (+ min max) 2))) a)) (/ (+ min max) 2) (+ 1 (/ (+ min max) 2))))) 20)))

(declare-const out Real)
(declare-const out1 Real)

(assert (= out (LOOKUP 7)))
(assert (= out1 (RECURSION 17 3 0 99)))
 
 
 