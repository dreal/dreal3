(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (* skoT (* skoT (/ 1. 2.))) (+ skoA (* skoB (- 1.))))) (and (not (<= (* skoT (* skoT (+ (+ (* skoA (+ 1. (* skoA (* skoA (- 1.))))) (* skoB (+ (+ (- 1.) (* skoA skoA)) (* skoB (+ (* skoA (+ (- 1.) (* skoA (/ 1. 2.)))) skoB))))) (* skoT (* skoT (+ (+ (* skoA (+ (- 1.) (* skoA (/ 1. 2.)))) (* skoB (+ 1. (* skoB (/ 1. 2.))))) (* skoT (* skoT (/ 1. 2.))))))))) (* skoB (* skoB (+ (* skoA (* skoA skoA)) (* skoB (* skoA (* skoA (- 1.))))))))) (and (not (<= (* skoT (* skoT (+ (+ (* skoA skoA) (* skoB skoB)) (* skoT skoT)))) (+ 1. (* skoB (* skoB (* skoA (* skoA (- 1.)))))))) (and (not (<= skoB skoA)) (and (not (<= 2. skoB)) (and (not (<= skoA 0.)) (not (= skoT 0.)))))))))
(set-info :status sat)
(check-sat)
