(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (not (= (* skoY (* skoX (- 1.))) (- 1.))) (and (not (= (* skoY (+ (* skoX (- 4.)) (* skoY (+ (* skoX (* skoX 6.)) (* skoY (+ (* skoX (* skoX (* skoX (- 4.)))) (* skoY (* skoX (* skoX (* skoX skoX)))))))))) (- 1.))) (and (not (= (* skoY (+ (* skoX (- 3.)) (* skoY (+ (* skoX (* skoX 3.)) (* skoY (* skoX (* skoX (* skoX (- 1.))))))))) (- 1.))) (and (not (= (* skoY (+ (* skoX (- 2.)) (* skoY (* skoX skoX)))) (- 1.))) (and (not (<= 0. skoX)) (and (not (<= skoZ 0.)) (and (not (<= skoX (- 1.))) (and (not (<= 1. skoY)) (not (<= skoY skoX)))))))))))
(set-info :status sat)
(check-sat)
