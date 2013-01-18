(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (* skoT (* skoT (/ (- 1.) 2.))) (+ (* skoA (- 1.)) skoB))) (and (not (<= skoB skoA)) (and (not (<= 2. skoB)) (and (not (<= skoA 0.)) (not (= skoT 0.)))))))
(set-info :status unsat)
(check-sat)
