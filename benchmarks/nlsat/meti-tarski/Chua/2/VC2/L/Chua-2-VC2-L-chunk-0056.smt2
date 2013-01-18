(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ (/ (- 1029.) 125.) (* skoX (/ 2499. 62500.)))) (- 612.))) (and (not (<= (* skoX (+ (+ (* skoC (/ 798. 125.)) (* skoS (/ (- 63.) 50.))) (* skoX (+ (* skoC (/ (- 931.) 31250.)) (* skoS (/ 147. 25000.)))))) (+ (* skoC 456.) (* skoS (- 90.))))) (or (not (<= (* skoC (/ 76. 15.)) skoS)) (not (<= skoS (* skoC (/ 76. 15.))))))))
(set-info :status sat)
(check-sat)
