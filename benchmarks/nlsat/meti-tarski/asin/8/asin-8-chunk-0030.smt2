(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoSP () Real)
(declare-fun skoSM () Real)
(assert (and (not (<= (+ (- 4.) (* skoSM (- 1.))) skoSP)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= skoX 0.)) (not (<= 1. skoX)))))))
(set-info :status sat)
(check-sat)
