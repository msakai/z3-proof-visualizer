(set-option :produce-proofs true)
(set-logic QF_LRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(assert (! (>= (+ x1 x2 x3) 1) :named c1))
(assert (! (>= (+ (- x1) x2) 0) :named c2))
(assert (! (>= (+ (- x2) x3) 0) :named c3))
(assert (! (>= (- x3) 0) :named c4))
(assert (! (>= (+ x2 (- x3)) 0) :named c5))
(assert (! (>= (+ (- x2) (- x3)) (- 1)) :named c6))
(assert (! (>= (+ (- x2) x3) 0) :named c7))
(check-sat)
;=> unsat
(get-proof)
;=>
;((set-logic QF_LRA)
;(proof
;(let ((?x68 (* (- 1.0) x3)))
;(let ((?x69 (+ x2 ?x68)))
;(let (($x70 (<= ?x69 0.0)))
;(let (($x58 (>= (+ (- x2) x3) 0.0)))
;(let ((@x64 (monotonicity (rewrite (= (- x2) (* (- 1.0) x2))) (= (+ (- x2) x3) (+ (* (- 1.0) x2) x3)))))
;(let ((@x74 (trans (monotonicity @x64 (= $x58 (>= (+ (* (- 1.0) x2) x3) 0.0))) (rewrite (= (>= (+ (* (- 1.0) x2) x3) 0.0) $x70)) (= $x58 $x70))))
;(let ((@x75 (mp (asserted $x58) @x74 $x70)))
;(let (($x32 (>= (+ x1 x2 x3) 1.0)))
;(let ((@x33 (asserted $x32)))
;(let (($x50 (<= (+ x1 (* (- 1.0) x2)) 0.0)))
;(let (($x36 (>= (+ (- x1) x2) 0.0)))
;(let ((@x44 (monotonicity (rewrite (= (- x1) (* (- 1.0) x1))) (= (+ (- x1) x2) (+ (* (- 1.0) x1) x2)))))
;(let ((@x54 (trans (monotonicity @x44 (= $x36 (>= (+ (* (- 1.0) x1) x2) 0.0))) (rewrite (= (>= (+ (* (- 1.0) x1) x2) 0.0) $x50)) (= $x36 $x50))))
;(let ((@x55 (mp (asserted $x36) @x54 $x50)))
;(let (($x84 (<= x3 0.0)))
;(let ((@x80 (rewrite (= (- x3) ?x68))))
;(let ((@x88 (trans (monotonicity @x80 (= (>= (- x3) 0.0) (>= ?x68 0.0))) (rewrite (= (>= ?x68 0.0) $x84)) (= (>= (- x3) 0.0) $x84))))
;(let ((@x89 (mp (asserted (>= (- x3) 0.0)) @x88 $x84)))
;((_ th-lemma arith farkas 3/2 1/2 1/2 1) @x89 @x55 @x33 @x75 false)))))))))))))))))))))