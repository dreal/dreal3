(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ (/ (- 574.) 1375.) (* skoX (/ 1813. 515625.)))) (/ (- 592.) 11.))) (and (not (<= (* skoX (+ (+ (* skoC (/ (- 112.) 165.)) (* skoS (/ 1029. 1375.))) (* skoX (+ (* skoC (/ 196. 61875.)) (* skoS (/ (- 2401.) 687500.)))))) (+ (* skoC (/ (- 1600.) 33.)) (* skoS (/ 588. 11.))))) (or (not (<= (* skoC (/ 400. 441.)) skoS)) (not (<= skoS (* skoC (/ 400. 441.))))))))
(set-info :status sat)
(check-sat)
