(define-sort A () (Array Int Int))

(declare-const s1 A)
(declare-const s2 A)

(declare-const s1_len Int)
(declare-const s2_len A)

(declare-fun length ((A)) Int)

(assert (= s1
  (store
    (store
      (store 
        (store 
        ((as const (Array Int Int)) -1) ; a way to declare a constant array with always -1
          0 1)
        1 2)
      2 3)
    3 4)
))

(assert (= (length s1) 4))
(assert (= (length s2) 4))

(assert (= (select s2 0) 1))
(assert (= (select s2 1) 2))
(assert (= (select s2 2) 3))
(assert (= (select s2 3) 4))

(define-fun array_contains ((arr A) (x Int)) Bool
	(exists ((i Int)) (and (>= i 0) (< i (length arr)) (= (select arr i) x))
))

(assert (array_contains s1 2))
(assert (array_contains s1 1))
(assert (array_contains s2 1))
(assert (array_contains s2 3))

(check-sat)
(get-model)
