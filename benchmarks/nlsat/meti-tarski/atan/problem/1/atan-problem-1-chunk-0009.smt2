(set-logic QF_NRA)

(declare-fun skoSX () Real)
(declare-fun skoX () Real)
(declare-fun skoS3 () Real)
(assert (and (not (= (* skoX (* skoX (- 80.))) (+ 75. (* skoSX (* skoSX (- 1.)))))) (and (not (<= skoX 0.)) (and (not (<= skoSX 0.)) (not (<= skoS3 0.))))))
(set-info :status sat)
(check-sat)
