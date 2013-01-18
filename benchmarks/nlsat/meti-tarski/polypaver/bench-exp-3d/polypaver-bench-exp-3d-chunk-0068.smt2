(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (+ (+ (+ (/ 135. 2.) (* skoX (+ 21. (* skoX (/ 27. 8.))))) (* skoY (+ (+ 21. (* skoX (/ 27. 4.))) (* skoY (/ 27. 8.))))) (* skoZ (+ (+ (+ (/ 21. 2.) (* skoX (/ 27. 8.))) (* skoY (/ 27. 8.))) (* skoZ (/ 9. 8.)))))) (+ (+ (- 105.) (* skoX (+ (/ (- 135.) 2.) (* skoX (+ (/ (- 21.) 2.) (* skoX (/ (- 9.) 8.))))))) (* skoY (+ (+ (/ (- 135.) 2.) (* skoX (+ (- 21.) (* skoX (/ (- 27.) 8.))))) (* skoY (+ (+ (/ (- 21.) 2.) (* skoX (/ (- 27.) 8.))) (* skoY (/ (- 9.) 8.)))))))) (and (<= (+ (+ 2. (* skoX (- 1.))) (* skoY (- 1.))) skoZ) (and (<= skoZ (+ (+ 2. (* skoX (- 1.))) (* skoY (- 1.)))) (and (<= skoZ 1.) (and (<= skoY 1.) (and (<= skoX 1.) (and (<= 0. skoZ) (and (<= 0. skoY) (<= 0. skoX))))))))))
(set-info :status unsat)
(check-sat)
