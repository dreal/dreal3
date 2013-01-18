(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (<= (* skoT (+ (* skoB (/ (- 157.) 100.)) (* skoT (+ 1. (* skoB (- 1.)))))) (* skoB (* skoA (- 1.)))) (and (not (<= (* skoT (+ (* skoB (/ 157. 100.)) (* skoT (+ (- 1.) skoB)))) (* skoB skoA))) (and (not (<= skoT (/ 3. 2.))) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA))))))))
(set-info :status sat)
(check-sat)
