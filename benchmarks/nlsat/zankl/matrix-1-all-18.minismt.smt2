(set-logic QF_NRA)
(set-info :source |
From termination analysis of term rewriting.

Submitted by Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun x3 () Real)
(declare-fun x0 () Real)
(declare-fun x4 () Real)
(declare-fun x1 () Real)
(declare-fun x5 () Real)
(declare-fun x2 () Real)
(assert (>= x3 0))
(assert (>= x0 0))
(assert (>= x4 0))
(assert (>= x1 0))
(assert (>= x5 0))
(assert (>= x2 0))
(assert (and (and (and (and (and (and (and (not (<= (+ (* x1 x2) (* (- 1) (* x4 x1)) (* (- 1) (* x1 x5 x2))) 0)) (>= (+ (* x1 x2) (* (- 1) (* x4 x1)) (* (- 1) (* x1 x5 x2))) 0)) (>= (+ (* x3 x1) (* (- 1) (* x3 x1 x5))) 0)) (and (and (not (<= (+ (* x1 x2) (* (- 1) (* x4 x1)) (* (- 1) (* x1 x5 x2)) (* (- 1) (* x3 x4 x1 x5)) (* (- 1) (* x3 x1 x5 x5 x2))) 0)) (>= (+ (* x1 x2) (* (- 1) (* x4 x1)) (* (- 1) (* x1 x5 x2)) (* (- 1) (* x3 x4 x1 x5)) (* (- 1) (* x3 x1 x5 x5 x2))) 0)) (>= (+ (* x3 x1) (* (- 1) (* x3 x3 x1 x5 x5))) 0))) (and (and (not (<= (* x1 x5 x2) 0)) (>= (* x1 x5 x2) 0)) (>= (+ (* (- 1) (* x1 x5)) (* x3 x1 x5)) 0))) (and (and (not (<= (+ (* x3 x2) (* (- 1) (* x3 x4)) (* (- 1) (* x3 x5 x2)) (* (- 1) (* x3 x3 x4 x5)) (* (- 1) (* x3 x3 x5 x5 x2))) 0)) (>= (+ (* x3 x2) (* (- 1) (* x3 x4)) (* (- 1) (* x3 x5 x2)) (* (- 1) (* x3 x3 x4 x5)) (* (- 1) (* x3 x3 x5 x5 x2))) 0)) (>= (+ (* x3 x3) (* (- 1) (* x3 x3 x3 x5 x5))) 0))) (and (and (not (<= (* x3 x5 x2) 0)) (>= (* x3 x5 x2) 0)) (>= (+ (* (- 1) (* x3 x5)) (* x3 x3 x5)) 0))) (and (and (and (and (not (<= (+ (* x1 x2) (* (- 1) (* x4 x1)) (* (- 1) (* x1 x5 x2))) 0)) (>= (+ (* x1 x2) (* (- 1) (* x4 x1)) (* (- 1) (* x1 x5 x2))) 0)) (>= (+ (* x3 x1) (* (- 1) (* x3 x1 x5))) 0)) (and (and (not (<= (+ (* x1 x2) (* (- 1) (* x4 x1)) (* (- 1) (* x1 x5 x2)) (* (- 1) (* x3 x4 x1 x5)) (* (- 1) (* x3 x1 x5 x5 x2))) 0)) (>= (+ (* x1 x2) (* (- 1) (* x4 x1)) (* (- 1) (* x1 x5 x2)) (* (- 1) (* x3 x4 x1 x5)) (* (- 1) (* x3 x1 x5 x5 x2))) 0)) (>= (+ (* x3 x1) (* (- 1) (* x3 x3 x1 x5 x5))) 0))) (and (and (not (<= (* x1 x5 x2) 0)) (>= (* x1 x5 x2) 0)) (>= (+ (* (- 1) (* x1 x5)) (* x3 x1 x5)) 0)))))
(exit)
(check-sat)
