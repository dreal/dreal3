(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoX)) (and (not (<= 0. skoY)) (and (not (<= (* skoZ (+ (+ (+ (- 9.) (* skoX (+ (/ (- 711.) 25.) (* skoX (+ (- 21.) (* skoX (/ (- 237.) 25.))))))) (* skoY (+ (+ (/ (- 711.) 25.) (* skoX (+ (- 18.) (* skoX (+ (/ 474. 25.) (* skoX (+ 18. (* skoX (/ 237. 25.))))))))) (* skoY (+ (+ (- 18.) (* skoX (+ (/ 711. 25.) (* skoX (+ 21. (* skoX (+ (/ 237. 25.) (* skoX 3.)))))))) (* skoY (* skoX (+ 18. (* skoX (* skoX 6.)))))))))) (* skoZ (+ (+ (/ (- 711.) 50.) (* skoX (+ (- 9.) (* skoX (/ (- 237.) 50.))))) (* skoY (+ (+ (- 9.) (* skoX (+ (/ 711. 25.) (* skoX (+ 15. (* skoX (/ 237. 25.))))))) (* skoY (+ (* skoX (+ 18. (* skoX (+ (/ (- 711.) 50.) (* skoX (+ (- 3.) (* skoX (/ (- 237.) 50.)))))))) (* skoY (* skoX (* skoX (+ (- 9.) (* skoX (* skoX (- 3.))))))))))))))) (+ (+ (/ 237. 50.) (* skoX (+ 12. (* skoX (+ (/ 79. 5.) (* skoX (+ 12. (* skoX (/ 237. 50.))))))))) (* skoY (+ (+ 12. (* skoX (+ (/ 474. 25.) (* skoX (+ 16. (* skoX (/ 158. 25.))))))) (* skoY (+ (+ (/ 711. 50.) (* skoX (+ 12. (* skoX (+ (/ 237. 25.) (* skoX (+ 4. (* skoX (/ 79. 50.))))))))) (* skoY (+ 9. (* skoX (* skoX (+ 6. (* skoX skoX))))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status sat)
(check-sat)
