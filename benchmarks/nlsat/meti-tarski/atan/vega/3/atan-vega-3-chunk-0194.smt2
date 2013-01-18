(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoY (+ (* skoX (- 3.)) (* skoY (+ 1. (* skoY (* skoX (- 1.))))))) (- 3.)) (and (<= (* skoY (+ (* skoX 3.) (* skoY (+ (- 1.) (* skoY skoX))))) 3.) (and (<= (* skoZ (+ 3. (* skoY (+ (* skoX (- 3.)) (* skoY (+ 1. (* skoY (* skoX (- 1.))))))))) (+ (* skoX (- 3.)) (* skoY (* skoY (+ (* skoX (- 4.)) (* skoY (- 1.))))))) (and (not (<= 0. skoY)) (and (or (not (<= 0. skoY)) (or (<= (* skoZ (+ (- 1.) (* skoY skoX))) (+ skoX skoY)) (<= (* skoZ (+ (+ 3. (* skoX skoX)) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))) (+ (* skoX (* skoX (* skoX (- 1.)))) (* skoY (+ (* skoX (* skoX (- 3.))) (* skoY (* skoX (+ (- 3.) (* skoX (* skoX (- 1.)))))))))))) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))
(set-info :status unsat)
(check-sat)
