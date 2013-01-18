(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoX (* skoX (* skoX (+ (/ 1. 6.) (* skoX (* skoX (+ (/ (- 1.) 120.) (* skoX (* skoX (/ 1. 5040.)))))))))) 0.)) (and (not (<= (* skoY (+ (* skoX (* skoX (/ 1. 6.))) (* skoY (* skoY (+ (/ (- 1.) 6.) (* skoY (* skoY (/ 1. 120.)))))))) 0.)) (and (not (<= skoX 0.)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= skoY skoX))))))))
(set-info :status sat)
(check-sat)
