(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (<= 0. skoA) (and (not (<= (* skoT (+ (* skoB (* skoB (* skoB (/ (- 157.) 100.)))) (* skoT (+ (* skoB (* skoB (+ 2. (* skoB (/ (- 3.) 10.))))) (* skoT (+ (* skoB (/ (- 157.) 100.)) (* skoT (+ 1. (* skoB (/ (- 3.) 10.)))))))))) (* skoB (* skoB (* skoB (* skoA (- 1.))))))) (and (not (<= skoB skoT)) (and (not (<= skoT 0.)) (and (not (<= skoB (* skoA (- 1.)))) (and (not (<= skoT 1.)) (not (<= skoB skoA)))))))))
(set-info :status sat)
(check-sat)
