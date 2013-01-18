(set-logic QF_NRA)

(declare-fun skoA () Real)
(declare-fun skoX () Real)
(declare-fun skoB () Real)
(assert (and (<= skoX (* skoA (- 1.))) (and (not (<= skoA 0.)) (and (not (<= skoB 0.)) (not (<= skoX 0.))))))
(set-info :status unsat)
(check-sat)

