(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoX () Real)
(declare-fun skoA () Real)
(assert (and (<= skoX (* skoB (- 1.))) (and (not (<= skoX 0.)) (and (not (<= skoB 0.)) (not (<= skoA 0.))))))
(set-info :status unsat)
(check-sat)
