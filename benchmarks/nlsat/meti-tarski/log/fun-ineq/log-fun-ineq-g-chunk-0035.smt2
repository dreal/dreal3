(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoX () Real)
(declare-fun skoA () Real)
(assert (and (<= (* skoX (+ (* skoB 2.) (* skoX 3.))) 0.) (and (not (<= (* skoB (* skoB (/ 3. 2.))) 0.)) (and (not (= skoX 0.)) (and (not (<= skoA 0.)) (and (not (<= skoB 0.)) (not (<= skoX 0.))))))))
(set-info :status unsat)
(check-sat)
