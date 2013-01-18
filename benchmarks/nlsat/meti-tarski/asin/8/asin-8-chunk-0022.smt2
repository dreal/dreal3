(set-logic QF_NRA)

(declare-fun skoSP () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (= (+ (- 1.) (* skoSP skoSP)) skoX)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= skoX 0.)) (not (<= 1. skoX)))))))
(set-info :status sat)
(check-sat)
