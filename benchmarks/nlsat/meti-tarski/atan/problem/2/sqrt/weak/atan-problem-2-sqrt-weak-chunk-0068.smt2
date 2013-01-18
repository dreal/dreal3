(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoA () Real)
(declare-fun skoB () Real)
(assert (and (<= (* skoT (+ (* skoA (/ 157. 100.)) (* skoT (+ 1. skoA)))) (* skoB (* skoA (- 1.)))) (and (not (<= skoT (/ 3. 2.))) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA)))))))
(set-info :status unsat)
(check-sat)
