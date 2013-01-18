(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoY)) (and (not (<= (* skoZ (+ (- 3.) (* skoY (+ (* skoX 3.) (* skoY (+ (- 1.) (* skoY skoX))))))) (+ (* skoX 3.) (* skoY (+ 3. (* skoY (+ skoX skoY))))))) (and (not (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (* skoX (- 1.)) (* skoY (- 1.))))) (and (not (<= (* skoZ (+ (+ (/ 819. 50.) (* skoX (+ (- 9.) (* skoX (/ 273. 50.))))) (* skoY (+ (+ (- 9.) (* skoX (+ (/ (- 819.) 50.) (* skoX (+ 6. (* skoX (/ (- 273.) 50.))))))) (* skoY (+ (+ (/ 273. 50.) (* skoX (+ 6. (* skoX (+ (/ 91. 50.) (* skoX 3.)))))) (* skoY (* skoX (+ (/ (- 273.) 50.) (* skoX (+ 3. (* skoX (/ (- 91.) 50.))))))))))))) (+ (+ 9. (* skoX (+ (/ (- 819.) 50.) (* skoX (+ 12. (* skoX (/ (- 273.) 50.))))))) (* skoY (+ (+ (/ (- 819.) 50.) (* skoX (+ 9. (* skoX (/ (- 273.) 50.))))) (* skoY (+ (+ 12. (* skoX (+ (/ (- 273.) 50.) (* skoX (+ 7. (* skoX (/ (- 91.) 50.))))))) (* skoY (+ (/ (- 273.) 50.) (* skoX (* skoX (+ (/ (- 91.) 50.) (* skoX (- 1.)))))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX))))))))))
(set-info :status unsat)
(check-sat)
