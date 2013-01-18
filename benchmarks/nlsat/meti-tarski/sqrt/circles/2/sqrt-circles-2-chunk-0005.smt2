(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoD () Real)
(assert (and (not (<= (* skoY (+ (- 2.) skoY)) (* skoX (* skoX (- 1.))))) (<= 0. skoD)))
(set-info :status sat)
(check-sat)
