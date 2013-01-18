(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoA () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoS skoB) 0.) (and (<= skoB 1.) (and (= (* skoS skoS) (+ (+ 1. (* skoA skoA)) (* skoB (* skoB (+ 1. (* skoA skoA)))))) (and (not (<= skoS 0.)) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA)))))))))
(set-info :status unsat)
(check-sat)
