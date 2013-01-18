(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoX (* skoX (+ (- 12012.) (* skoX (* skoX (+ (- 6930.) (* skoX (* skoX (+ (- 1260.) (* skoX (* skoX (- 35.)))))))))))) 6435.)) (and (not (<= 0. skoY)) (and (not (<= 0. skoX)) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status unsat)
(check-sat)
