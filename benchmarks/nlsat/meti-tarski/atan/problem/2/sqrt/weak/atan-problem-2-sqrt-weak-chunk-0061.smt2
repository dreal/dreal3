(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoA () Real)
(declare-fun skoT () Real)
(assert (and (<= (* skoT (+ (* skoA (- 1.)) (* skoB (+ 1. skoA)))) (* skoB (* skoA (/ (- 157.) 50.)))) (and (not (<= skoB skoA)) (and (not (<= 2. skoB)) (and (not (<= skoA 0.)) (not (<= skoT (/ 3. 2.))))))))
(set-info :status unsat)
(check-sat)
