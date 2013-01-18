(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoA () Real)
(declare-fun skoD () Real)
(assert (and (not (<= (* skoY (+ (* skoA (- 2.)) skoY)) (* skoX (* skoX (- 1.))))) (and (<= 0. skoD) (<= 0. skoA))))
(set-info :status sat)
(check-sat)
