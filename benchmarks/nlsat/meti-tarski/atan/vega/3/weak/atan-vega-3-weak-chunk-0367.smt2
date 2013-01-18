(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoZ (+ (+ (* skoX (- 6.)) (* skoY (+ (+ (- 6.) (* skoX (* skoX 6.))) (* skoY (* skoX 6.))))) (* skoZ (+ (- 3.) (* skoY (+ (* skoX 6.) (* skoY (* skoX (* skoX (- 3.)))))))))) (+ (+ 1. (* skoX (* skoX 3.))) (* skoY (+ (* skoX 4.) (* skoY (+ 3. (* skoX skoX)))))))) (and (not (<= (* skoZ (+ (+ (+ (- 3.) (* skoX (+ (/ (- 399.) 50.) (* skoX (- 6.))))) (* skoY (+ (+ (/ (- 399.) 50.) (* skoX (+ (- 6.) (* skoX (+ (/ 399. 50.) (* skoX 6.)))))) (* skoY (+ (+ (- 6.) (* skoX (+ (/ 399. 50.) (* skoX 9.)))) (* skoY (* skoX 6.))))))) (* skoZ (+ (+ (/ (- 399.) 100.) (* skoX (- 3.))) (* skoY (+ (+ (- 3.) (* skoX (+ (/ 399. 50.) (* skoX 6.)))) (* skoY (+ (* skoX (+ 6. (* skoX (+ (/ (- 399.) 100.) (* skoX (- 3.)))))) (* skoY (* skoX (* skoX (- 3.)))))))))))) (+ (+ (/ 133. 100.) (* skoX (+ 4. (* skoX (+ (/ 399. 100.) (* skoX 3.)))))) (* skoY (+ (+ 4. (* skoX (+ (/ 133. 25.) (* skoX 4.)))) (* skoY (+ (+ (/ 399. 100.) (* skoX (+ 4. (* skoX (+ (/ 133. 100.) skoX))))) (* skoY (+ 3. (* skoX skoX)))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))
(set-info :status unsat)
(check-sat)
