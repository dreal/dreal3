(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS3 () Real)
(declare-fun skoSX () Real)
(assert (and (not (<= (* skoX (+ (+ (* skoS3 (/ 1413711. 20000.)) (* skoSX (/ 471237. 20000.))) (* skoX (+ (+ (* skoS3 (- 267.)) (* skoSX (- 49.))) (* skoX (+ (+ (* skoS3 (/ 3298659. 10000.)) (* skoSX (/ 1099553. 10000.))) (* skoX (+ (+ (* skoS3 (- 749.)) (* skoSX (- 63.))) (* skoX (+ (+ (* skoS3 (/ 29687931. 100000.)) (* skoSX (/ 9895977. 100000.))) (* skoX (* skoS3 (- 504.))))))))))))) (+ (* skoS3 (/ 64. 5.)) (* skoSX (/ 64. 15.))))) (and (not (<= skoX 0.)) (and (not (<= skoSX 0.)) (not (<= skoS3 0.))))))
(set-info :status sat)
(check-sat)
