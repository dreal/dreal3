(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoS () Real)
(declare-fun skoA () Real)
(assert (and (<= (* skoT (+ (* skoS (* skoB (/ 157. 100.))) (* skoT (+ (* skoB (+ skoA (* skoB (- 1.)))) (* skoS (+ (- 1.) (* skoB (/ 1. 10.)))))))) (* skoS (* skoB skoA))) (and (not (<= (* skoS skoB) 0.)) (and (not (<= skoT 0.)) (and (= (* skoT (* skoT (+ (+ (* skoA (* skoA (- 1.))) (* skoB (* skoB (- 1.)))) (* skoT (* skoT (- 1.)))))) (+ (* skoB (* skoB (* skoA skoA))) (* skoS (* skoS (- 1.))))) (and (<= 0. skoS) (and (not (= skoT 0.)) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA)))))))))))
(set-info :status sat)
(check-sat)
