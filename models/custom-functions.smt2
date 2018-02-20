(set-option :smt.mbqi true)

(define-fun LOOKUP ((x Real)) Real
  (ite (= x 0.0) 0.0 (ite (and (> x 0) (< x 20)) (/ (* x 147) 2) (ite (= x 20) 1470 (ite (and (> x 20) (< x 30)) (- 1470 (* 49 (- x 20))) 980)))))

(define-fun-rec R ((a Real) (b Real) (min Int) (max Int)) Real
    (ite (= min max) (+ 1 max) (ite (> max min) (ite (< a (* b (/ (+ min max) 2))) (R a b min (to_int (/ (+ min max) 2))) (ite (> a (* b (+ 1 (/ (+ min max) 2)))) (R a b (+ (to_int (/ (+ min max) 2)) 1) max) (ite (<= (* b (- a (/ (+ min max) 2))) (- (* b (+ 1 (/ (+ min max) 2))) a)) (/ (+ min max) 2) (+ 1 (/ (+ min max) 2))))) 20)))

(define-fun BSR ((m Real) (g Real)) Real (ite (or (= m 0) (= g 0)) 0 (ite (> m (* 100 g)) 100 (R m g 0 99))))
