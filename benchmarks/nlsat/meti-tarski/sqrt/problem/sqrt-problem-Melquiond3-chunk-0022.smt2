(set-logic QF_NRA)

(declare-fun skoSXY () Real)
(declare-fun skoT () Real)
(declare-fun skoX () Real)
(declare-fun skoY () Real)
(assert (and (not (= (+ (* skoSXY (- 1.)) (* skoT (* skoT skoSXY))) skoX)) (and (= (+ (* skoSXY skoSXY) (* skoX (- 1.))) skoY) (and (<= skoY (/ 33. 32.)) (and (<= skoX 2.) (and (<= (/ 3. 2.) skoX) (and (<= 1. skoY) (and (<= 0. skoT) (<= 0. skoSXY)))))))))
(set-info :status sat)
(check-sat)
