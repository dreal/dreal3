(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoC (/ 3. 13.)) skoS)) (not (<= (* skoX (+ (/ (- 693.) 62500000.) (* skoX (/ 693. 1562500000000.)))) (/ (- 231.) 2500.)))))
(set-info :status sat)
(check-sat)
