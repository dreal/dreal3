(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (not (<= (* skoY (+ (* skoX (- 6435.)) (* skoY (+ 12012. (* skoY (+ (* skoX (- 12012.)) (* skoY (+ 6930. (* skoY (+ (* skoX (- 6930.)) (* skoY (+ 1260. (* skoY (+ (* skoX (- 1260.)) (* skoY (+ 35. (* skoY (* skoX (- 35.))))))))))))))))))) (- 6435.))) (and (not (<= 0. skoY)) (and (not (<= 0. skoX)) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))
(set-info :status sat)
(check-sat)
