(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (+ 3. (* skoX skoX)) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))) (+ (* skoX (* skoX (* skoX (- 1.)))) (* skoY (+ (* skoX (* skoX (- 3.))) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.))))))))))) (and (not (<= (* skoZ (+ (+ (+ 9. (* skoX (* skoX (- 3.)))) (* skoY (+ (* skoX (+ (- 30.) (* skoX (* skoX (- 2.))))) (* skoY (+ (+ (- 6.) (* skoX (* skoX (+ 19. (* skoX (* skoX 5.)))))) (* skoY (* skoX (+ 6. (* skoX (* skoX 2.)))))))))) (* skoZ (+ (* skoX (- 3.)) (* skoY (+ (+ (- 3.) (* skoX (* skoX 5.))) (* skoY (+ (* skoX (+ 6. (* skoX (* skoX (- 1.))))) (* skoY (* skoX (* skoX (+ (- 3.) (* skoX (* skoX (- 1.))))))))))))))) (* skoY (+ (* skoX (* skoX (* skoX (* skoX 4.)))) (* skoY (+ (* skoX (* skoX (* skoX 8.))) (* skoY (+ 3. (* skoX (* skoX (+ 10. (* skoX (* skoX 3.))))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))
(set-info :status sat)
(check-sat)
