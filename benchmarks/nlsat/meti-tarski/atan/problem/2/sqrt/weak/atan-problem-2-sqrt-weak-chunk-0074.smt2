(set-logic QF_NRA)

(declare-fun skoA () Real)
(declare-fun skoT () Real)
(declare-fun skoB () Real)
(assert (and (<= (* skoT (* skoT (+ (* skoA (* skoA (- 1.))) (* skoB skoA)))) 0.) (and (not (<= skoT (/ 3. 2.))) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA)))))))
(set-info :status unsat)
(check-sat)
