(set-logic QF_NRA)

(declare-fun skoA () Real)
(declare-fun skoY () Real)
(declare-fun skoD () Real)
(declare-fun skoX () Real)
(assert (and (or (not (<= (* skoY (+ (* skoA (- 2.)) skoY)) (+ (+ 1. (* skoA (* skoA (- 1.)))) (* skoX (* skoX (- 1.)))))) (<= (* skoY (+ (* skoA (- 2.)) skoY)) (+ (* skoA (+ 1. (* skoA (- 1.)))) (* skoX (* skoX (- 1.)))))) (and (not (<= (* skoY (+ (+ (* skoA (- 1.)) (* skoD (- 1.))) (* skoY (/ 1. 2.)))) (+ (+ (+ (/ (- 1.) 2.) (* skoA (+ 1. (* skoA (/ (- 1.) 2.))))) (* skoD (+ (+ 1. (* skoA (- 1.))) (* skoD (/ (- 1.) 2.))))) (* skoX (* skoX (/ (- 1.) 2.)))))) (and (<= (* skoY (+ (* skoA (- 2.)) skoY)) (* skoX (* skoX (- 1.)))) (and (<= 0. skoD) (<= 0. skoA))))))
(set-info :status sat)
(check-sat)
