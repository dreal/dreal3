(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (not (<= skoS (* skoC (/ 3. 13.)))) (and (not (<= skoX 0.)) (or (not (<= (* skoC (/ 3. 13.)) skoS)) (not (<= skoS (* skoC (/ 3. 13.))))))))
(set-info :status sat)
(check-sat)
