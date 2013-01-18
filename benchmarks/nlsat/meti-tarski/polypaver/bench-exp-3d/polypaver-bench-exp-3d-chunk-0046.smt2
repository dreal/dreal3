(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= skoZ (+ (+ (/ 3. 2.) (* skoX (- 1.))) (* skoY (- 1.)))) (and (not (<= skoZ (+ (+ 2. (* skoX (- 1.))) (* skoY (- 1.))))) (and (<= skoZ 1.) (and (<= skoY 1.) (and (<= skoX 1.) (and (<= 0. skoZ) (and (<= 0. skoY) (<= 0. skoX)))))))))
(set-info :status unsat)
(check-sat)
