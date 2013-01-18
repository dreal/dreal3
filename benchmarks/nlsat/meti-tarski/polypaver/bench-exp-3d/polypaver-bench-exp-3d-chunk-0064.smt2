(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (not (<= (* skoZ (+ (+ (+ (/ 135. 2.) (* skoX (+ 21. (* skoX (/ 27. 8.))))) (* skoY (+ (+ 21. (* skoX (/ 27. 4.))) (* skoY (/ 27. 8.))))) (* skoZ (+ (+ (+ (/ 21. 2.) (* skoX (/ 27. 8.))) (* skoY (/ 27. 8.))) (* skoZ (/ 9. 8.)))))) (+ (+ (- 105.) (* skoX (+ (/ (- 135.) 2.) (* skoX (+ (/ (- 21.) 2.) (* skoX (/ (- 9.) 8.))))))) (* skoY (+ (+ (/ (- 135.) 2.) (* skoX (+ (- 21.) (* skoX (/ (- 27.) 8.))))) (* skoY (+ (+ (/ (- 21.) 2.) (* skoX (/ (- 27.) 8.))) (* skoY (/ (- 9.) 8.))))))))))
(set-info :status sat)
(check-sat)
