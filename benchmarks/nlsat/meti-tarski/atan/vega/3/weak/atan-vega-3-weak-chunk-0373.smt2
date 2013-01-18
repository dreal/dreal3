(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (+ (+ (+ 3. (* skoX (+ (/ 399. 50.) (* skoX 6.)))) (* skoY (+ (+ (/ 399. 50.) (* skoX (+ 6. (* skoX (+ (/ (- 399.) 50.) (* skoX (- 6.))))))) (* skoY (+ (+ 6. (* skoX (+ (/ (- 399.) 50.) (* skoX (- 9.))))) (* skoY (* skoX (- 6.)))))))) (* skoZ (+ (+ (/ 399. 100.) (* skoX 3.)) (* skoY (+ (+ 3. (* skoX (+ (/ (- 399.) 50.) (* skoX (- 6.))))) (* skoY (+ (* skoX (+ (- 6.) (* skoX (+ (/ 399. 100.) (* skoX 3.))))) (* skoY (* skoX (* skoX 3.))))))))))) (+ (+ (/ (- 133.) 100.) (* skoX (+ (- 4.) (* skoX (+ (/ (- 399.) 100.) (* skoX (- 3.))))))) (* skoY (+ (+ (- 4.) (* skoX (+ (/ (- 133.) 25.) (* skoX (- 4.))))) (* skoY (+ (+ (/ (- 399.) 100.) (* skoX (+ (- 4.) (* skoX (+ (/ (- 133.) 100.) (* skoX (- 1.))))))) (* skoY (+ (- 3.) (* skoX (* skoX (- 1.))))))))))) (and (not (<= 0. skoX)) (and (or (<= 0. skoY) (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (or (not (<= 0. skoY)) (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))))
(set-info :status sat)
(check-sat)
