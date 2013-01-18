(set-logic QF_NRA)

(declare-fun skoX7 () Real)
(declare-fun skoX6 () Real)
(declare-fun skoX5 () Real)
(declare-fun skoX8 () Real)
(declare-fun skoX3 () Real)
(declare-fun skoX1 () Real)
(declare-fun skoX2 () Real)
(declare-fun skoX4 () Real)
(assert (not (<= (* skoX8 (+ (* skoX5 (* skoX5 (* skoX4 (- 3.)))) (* skoX8 (+ (* skoX5 (* skoX2 (- 3.))) (* skoX8 skoX4))))) (+ (+ (+ (/ 7871547. 10000000.) (* skoX5 (* skoX5 (* skoX5 (* skoX2 (- 1.)))))) (* skoX6 (* skoX6 (* skoX6 (* skoX1 (- 1.)))))) (* skoX7 (+ (* skoX6 (* skoX6 (* skoX3 3.))) (* skoX7 (+ (* skoX6 (* skoX1 3.)) (* skoX7 (* skoX3 (- 1.)))))))))))
(set-info :status sat)
(check-sat)

