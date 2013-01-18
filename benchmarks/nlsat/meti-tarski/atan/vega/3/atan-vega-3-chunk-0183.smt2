(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= 0. skoX)) (and (not (<= (* skoZ (+ 1. (* skoY (* skoX (- 1.))))) (+ (+ 1. (* skoX (- 1.))) (* skoY (+ (- 1.) (* skoX (- 1.))))))) (and (not (<= (* skoZ (+ (+ (/ 471. 100.) (* skoX (+ (- 3.) (* skoX (/ 157. 100.))))) (* skoY (+ (+ (- 3.) (* skoX (+ (/ (- 471.) 100.) (* skoX (+ 2. (* skoX (/ (- 157.) 100.))))))) (* skoY (* skoX (+ 3. (* skoX skoX)))))))) (+ (+ 3. (* skoX (+ (/ (- 471.) 100.) (* skoX (+ 4. (* skoX (/ (- 157.) 100.))))))) (* skoY (+ (+ (/ (- 471.) 100.) (* skoX (+ 3. (* skoX (/ (- 157.) 100.))))) (* skoY (+ 3. (* skoX skoX)))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status sat)
(check-sat)
