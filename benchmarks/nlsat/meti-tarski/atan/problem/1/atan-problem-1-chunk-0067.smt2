(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS3 () Real)
(declare-fun skoSX () Real)
(assert (and (not (<= (* skoX (+ (- 15.) (* skoX (* skoX (+ (- 70.) (* skoX (* skoX (- 63.)))))))) 0.)) (and (not (<= skoX 0.)) (and (not (<= skoSX 0.)) (not (<= skoS3 0.))))))
(set-info :status unsat)
(check-sat)
