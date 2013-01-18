(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoY (* skoY (+ (- 12012.) (* skoY (* skoY (+ (- 6930.) (* skoY (* skoY (+ (- 1260.) (* skoY (* skoY (- 35.)))))))))))) 6435.)) (and (not (<= 0. skoY)) (and (not (<= 0. skoX)) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status unsat)
(check-sat)
