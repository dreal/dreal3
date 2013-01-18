(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSQ3 () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (+ (/ (- 3.) 2.) (* skoSQ3 (* skoSQ3 (/ 1. 2.)))))))))) (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (/ 1. 12.))))))) (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (/ 1. 720.))))) (* skoX (* skoX (+ (* skoSQ3 (* skoSQ3 (/ (- 1.) 40320.))) (* skoX (* skoX (/ 1. 3628800.))))))))))))))) (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (* skoSQ3 (+ (- 3.) (* skoSQ3 skoSQ3)))))))))) (and (not (<= (+ (/ (- 1.) 10000000.) (* pi (/ 1. 2.))) skoX)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= skoX 0.)) (not (<= skoSQ3 0.))))))))
(set-info :status sat)
(check-sat)
