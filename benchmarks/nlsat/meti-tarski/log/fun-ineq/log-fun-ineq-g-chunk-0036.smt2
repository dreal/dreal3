(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoA () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoB (* skoB (/ 3. 2.))) 0.) (and (not (= skoX 0.)) (and (not (<= skoA 0.)) (and (not (<= skoB 0.)) (not (<= skoX 0.)))))))
(set-info :status unsat)
(check-sat)
