(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoS () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (* skoS (* skoB (- 1.))) 0.)) (and (not (<= (* skoS (+ (- 1.) (* skoB (+ (/ 207. 100.) (* skoA (- 1.)))))) (* skoB (+ (* skoA (- 1.)) skoB)))) (and (not (<= skoB 1.)) (and (not (<= skoS 0.)) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA)))))))))
(set-info :status unsat)
(check-sat)
