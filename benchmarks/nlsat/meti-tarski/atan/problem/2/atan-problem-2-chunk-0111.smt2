(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoS (* skoB (- 1.))) 0.) (and (<= (* skoS skoB) 0.) (and (<= (* skoT (+ (* skoB (+ skoA (* skoB (- 1.)))) (* skoS (+ (- 1.) (* skoB (/ 1. 10.)))))) (* skoS (* skoB (/ (- 157.) 100.)))) (and (not (<= skoT 0.)) (and (= (* skoT (* skoT (+ (+ (* skoA (* skoA (- 1.))) (* skoB (* skoB (- 1.)))) (* skoT (* skoT (- 1.)))))) (+ (* skoB (* skoB (* skoA skoA))) (* skoS (* skoS (- 1.))))) (and (<= 0. skoS) (and (not (= skoT 0.)) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA))))))))))))
(set-info :status unsat)
(check-sat)
