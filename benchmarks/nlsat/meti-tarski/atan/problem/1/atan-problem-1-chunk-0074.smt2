(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS3 () Real)
(declare-fun skoSX () Real)
(assert (and (<= (* skoX (+ 15. (* skoX (* skoX (+ 70. (* skoX (* skoX 63.))))))) 0.) (and (not (<= (* skoX (+ (+ (* skoS3 (/ 1413711. 20000.)) (* skoSX (/ 471237. 20000.))) (* skoX (+ (+ (* skoS3 (- 267.)) (* skoSX (- 49.))) (* skoX (+ (+ (* skoS3 (/ 3298659. 10000.)) (* skoSX (/ 1099553. 10000.))) (* skoX (+ (+ (* skoS3 (- 749.)) (* skoSX (- 63.))) (* skoX (+ (+ (* skoS3 (/ 29687931. 100000.)) (* skoSX (/ 9895977. 100000.))) (* skoX (* skoS3 (- 504.))))))))))))) (+ (* skoS3 (/ 64. 5.)) (* skoSX (/ 64. 15.))))) (and (not (<= skoX 1.)) (and (<= (* skoX (+ (+ (* skoS3 (/ 471. 100.)) (* skoSX (/ 157. 100.))) (* skoX (* skoS3 (- 8.))))) (+ (* skoS3 3.) skoSX)) (and (= (* skoX (* skoX (- 80.))) (+ 75. (* skoSX (* skoSX (- 1.))))) (and (= (* skoS3 skoS3) 3.) (and (not (<= skoX 0.)) (and (not (<= skoSX 0.)) (not (<= skoS3 0.)))))))))))
(set-info :status unsat)
(check-sat)
