(set-logic QF_NRA)

(declare-fun skoA () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= (* skoA (/ 1. 2000.)) skoX)) (and (not (<= (* skoX (+ (* skoA (* skoA (* skoA (+ (/ 1. 6.) (* skoA (* skoA (+ (/ (- 1.) 120.) (* skoA (* skoA (+ (/ 1. 5040.) (* skoA (* skoA (/ (- 1.) 362880.))))))))))))) (* skoX (* skoX (* skoA (/ (- 1.) 6.)))))) (* skoA (* skoA (+ (/ (- 1.) 2000.) (* skoA (* skoA (+ (/ 1. 12000.) (* skoA (* skoA (+ (/ (- 1.) 240000.) (* skoA (* skoA (+ (/ 1. 10080000.) (* skoA (* skoA (/ (- 1.) 725760000.))))))))))))))))) (and (not (<= (* skoX (+ (* skoA (* skoA (* skoA (+ (/ (- 1.) 6.) (* skoA (* skoA (/ 1. 120.))))))) (* skoX (* skoX (+ (* skoA (/ 1. 6.)) (* skoX (* skoX (+ (* skoA (/ (- 1.) 120.)) (* skoX (* skoX (* skoA (/ 1. 5040.)))))))))))) (* skoA (* skoA (+ (/ 1. 2000.) (* skoA (* skoA (+ (/ (- 1.) 12000.) (* skoA (* skoA (/ 1. 240000.))))))))))) (and (not (<= (* skoX (+ (* skoA (* skoA (* skoA (+ (/ (- 1.) 6.) (* skoA (* skoA (/ 1. 120.))))))) (* skoX (* skoX (* skoA (/ 1. 6.)))))) (* skoA (* skoA (+ (/ 1. 2000.) (* skoA (* skoA (+ (/ (- 1.) 12000.) (* skoA (* skoA (/ 1. 240000.))))))))))) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= (* pi (/ 1. 2.)) skoA)) (and (not (<= skoX 0.)) (and (not (<= skoA skoX)) (or (not (<= (* skoA (/ 1. 2000.)) skoX)) (not (<= skoX (* skoA (/ 1. 2000.)))))))))))))))
(set-info :status unsat)
(check-sat)
