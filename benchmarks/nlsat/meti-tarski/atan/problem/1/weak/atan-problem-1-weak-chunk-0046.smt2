(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoY () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (* skoX (+ (- 231.) (* skoX (* skoX (+ (- 238.) (* skoX (* skoX (/ (- 231.) 5.))))))))) (* skoY (* skoX (+ (- 1155.) (* skoX (* skoX (+ (- 1806.) (* skoX (* skoX (+ (/ (- 3507.) 5.) (* skoX (* skoX (- 40.))))))))))))) (and (not (<= (* skoY (- 3.)) skoZ)) (and (= (* skoZ skoZ) (+ 75. (* skoX (* skoX 80.)))) (and (= (* skoY skoY) 3.) (and (<= skoX 1.) (and (<= 0. skoZ) (and (<= 0. skoY) (not (<= skoX 0.))))))))))
(set-info :status unsat)
(check-sat)
