(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS3 () Real)
(declare-fun skoSX () Real)
(assert (and (not (<= (* skoX (+ (+ (* skoS3 (- 1155.)) (* skoSX 231.)) (* skoX (* skoX (+ (+ (* skoS3 (- 1806.)) (* skoSX 238.)) (* skoX (* skoX (+ (+ (* skoS3 (/ (- 3507.) 5.)) (* skoSX (/ 231. 5.))) (* skoX (* skoX (* skoS3 (- 40.)))))))))))) 0.)) (and (not (<= skoX 0.)) (and (not (<= skoSX 0.)) (not (<= skoS3 0.))))))
(set-info :status sat)
(check-sat)
