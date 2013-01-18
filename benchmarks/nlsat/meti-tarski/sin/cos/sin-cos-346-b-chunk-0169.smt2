(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoX (* skoX (* skoX (* skoX (+ (/ 1. 24.) (* skoX (* skoX (+ (/ (- 1.) 720.) (* skoX (* skoX (/ 1. 40320.))))))))))) (+ (- 3.) (* skoSQ3 skoSQ3)))) (and (= (* skoSQ3 skoSQ3) 3.) (and (not (<= (+ (/ (- 1.) 10000000.) (* pi (/ 1. 2.))) skoX)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= skoX 0.)) (not (<= skoSQ3 0.)))))))))
(set-info :status sat)
(check-sat)
