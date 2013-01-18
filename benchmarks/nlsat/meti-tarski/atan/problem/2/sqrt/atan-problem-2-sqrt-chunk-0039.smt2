(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (* skoT (* skoT (+ (+ (* skoA skoA) (* skoB skoB)) (* skoT skoT)))) (+ 1. (* skoB (* skoB (* skoA (* skoA (- 1.)))))))) (and (not (<= skoB skoA)) (and (not (<= 2. skoB)) (and (not (<= skoA 0.)) (not (= skoT 0.)))))))
(set-info :status sat)
(check-sat)
