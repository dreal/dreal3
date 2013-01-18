(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (not (<= 0. skoB)) (and (not (<= (* skoT (+ (* skoB (* skoB (* skoA (/ 157. 100.)))) (* skoT (+ (+ (* skoA skoA) (* skoB (* skoB (+ 1. (* skoA (/ 3. 10.)))))) (* skoT (+ (* skoA (/ 157. 100.)) (* skoT (+ 1. (* skoA (/ 3. 10.)))))))))) (* skoB (* skoB (* skoB (* skoA (- 1.))))))) (and (not (<= skoT 0.)) (and (not (<= skoB (* skoA (- 1.)))) (and (not (<= skoT 1.)) (not (<= skoB skoA))))))))
(set-info :status unsat)
(check-sat)
