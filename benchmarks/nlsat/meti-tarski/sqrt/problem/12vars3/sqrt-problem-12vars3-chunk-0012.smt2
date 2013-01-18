(set-logic QF_NRA)

(declare-fun skoSX () Real)
(declare-fun skoX () Real)
(declare-fun skoSMX () Real)
(assert (and (not (= (+ (- 1.) (* skoSX skoSX)) skoX)) (and (<= skoX 1.) (and (<= 0. skoSX) (and (<= 0. skoSMX) (not (<= skoX 0.)))))))
(set-info :status sat)
(check-sat)
