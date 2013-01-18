(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSX () Real)
(declare-fun skoSMX () Real)
(assert (and (not (<= (+ (- 4.) (* skoSMX (- 1.))) skoSX)) (not (<= skoX 0.))))
(set-info :status sat)
(check-sat)
