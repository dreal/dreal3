(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoA () Real)
(declare-fun skoB () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoT (+ (* skoS (* skoA (/ (- 157.) 100.))) (* skoT (+ (+ (* skoA skoA) (* skoB (* skoA (- 1.)))) (* skoS (+ 1. skoA)))))) (* skoS (* skoB (* skoA (- 1.))))) (and (not (<= 0. skoT)) (and (or (not (<= (- 1.) skoT)) (<= 0. skoT)) (and (or (not (<= 0. skoT)) (not (<= skoT 1.))) (and (= (* skoT (* skoT (+ (+ (* skoA (* skoA (- 1.))) (* skoB (* skoB (- 1.)))) (* skoT (* skoT (- 1.)))))) (+ (* skoB (* skoB (* skoA skoA))) (* skoS (* skoS (- 1.))))) (and (<= 0. skoS) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA)))))))))))
(set-info :status unsat)
(check-sat)
