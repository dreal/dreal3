(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS3 () Real)
(declare-fun skoSX () Real)
(assert (and (<= (* skoX (+ (- 15.) (* skoX (* skoX (+ (- 70.) (* skoX (* skoX (- 63.)))))))) 0.) (and (<= (* skoX (+ (+ (* skoS3 (/ 471. 100.)) (* skoSX (/ 157. 100.))) (* skoX (* skoS3 (- 8.))))) (+ (* skoS3 3.) skoSX)) (and (= (* skoX (* skoX (- 80.))) (+ 75. (* skoSX (* skoSX (- 1.))))) (and (= (* skoS3 skoS3) 3.) (and (not (<= skoX 0.)) (and (not (<= skoSX 0.)) (not (<= skoS3 0.)))))))))
(set-info :status sat)
(check-sat)
