(define-fun-rec R ((a Real) (b Real) (min Int) (max Int)) Real
  (ite
    ;condition
    (= min max)
    ;then
    (+ 1 max)
    ;else
    (ite
      ;condition
      (> max min)
      ;then ite 1
      (ite
        ;condition
        (< a (* b (/ (+ min max) 2)))
        ;then
        (R a b min (to_int (/ (+ min max) 2)))
        ;else ite2
        (ite
          ;condition
          (> a (* b (+ 1 (/ (+ min max) 2))))
          ;then
          (R a b (+ (to_int (/ (+ min max) 2)) 1) max)
          ;else ite 3
          (ite
            ;condition
            (<= (* b (- a (/ (+ min max) 2)))
              (- (* b (+ 1 (/ (+ min max) 2))) a)
            )
            ;then
            (/ (+ min max) 2)
            ;else
            (+ 1 (/ (+ min max) 2))
          )
        )
      )
      ;else
      27
    )
  )
)

(define-fun BSR ((a Real) (b Real)) Real
  (ite
    ;condition
    (or (= a 0) (= b 0))
    ;then
    0
    ;else
    (ite
      ;condition
      (> a (* 100 b))
      ;then
      100
      ;else
      (R a b 0 99)
    )
   )
)


(define-fun LOOKUP ((x Real)) Real
  (ite
    ;condition
    (= x 0.0)
    ;then
    0.0
    ;else
    (ite
      ;condition
      (and (> x 0) (< x 20))
      ;then
      (/ (* x 147) 2)
      ;else
      (ite
        ;condition
        (= x 20)
        ;then
        1470
        ;else
        (ite
          ;condition
          (and (> x 20) (< x 30))
          ;then
          (- 1470 (* 49 (- x 20)))
          ;else
          980
        )
       )
    )
  )
)
