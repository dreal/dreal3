(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (* skoX (+ (/ (- 567.) 6250000.) (* skoX (/ 567. 156250000000.)))) (/ (- 189.) 250.))) (not (<= skoS (* skoC (/ 1770. 689.))))))
(set-info :status sat)
(check-sat)
