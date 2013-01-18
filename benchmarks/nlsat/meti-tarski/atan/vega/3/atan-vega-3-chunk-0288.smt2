(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoX skoX) (- 3.)) (and (not (<= 0. skoY)) (and (not (<= (* skoZ (+ (+ (/ 1413. 100.) (* skoX (+ (- 9.) (* skoX (/ 471. 100.))))) (* skoY (+ (+ (- 9.) (* skoX (+ (/ (- 1413.) 100.) (* skoX (+ 6. (* skoX (/ (- 471.) 100.))))))) (* skoY (+ (+ (/ 471. 100.) (* skoX (+ 6. (* skoX (+ (/ 157. 100.) (* skoX 3.)))))) (* skoY (* skoX (+ (/ (- 471.) 100.) (* skoX (+ 3. (* skoX (/ (- 157.) 100.))))))))))))) (+ (+ 9. (* skoX (+ (/ (- 1413.) 100.) (* skoX (+ 12. (* skoX (/ (- 471.) 100.))))))) (* skoY (+ (+ (/ (- 1413.) 100.) (* skoX (+ 9. (* skoX (/ (- 471.) 100.))))) (* skoY (+ (+ 12. (* skoX (+ (/ (- 471.) 100.) (* skoX (+ 7. (* skoX (/ (- 157.) 100.))))))) (* skoY (+ (/ (- 471.) 100.) (* skoX (* skoX (+ (/ (- 157.) 100.) (* skoX (- 1.)))))))))))))) (and (or (not (<= 0. skoY)) (or (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY)) (<= (* skoZ (+ (+ 3. (* skoX skoX)) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))) (+ (* skoX (* skoX (* skoX (- 1.)))) (* skoY (+ (* skoX (* skoX (- 3.))) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))))
(set-info :status unsat)
(check-sat)
