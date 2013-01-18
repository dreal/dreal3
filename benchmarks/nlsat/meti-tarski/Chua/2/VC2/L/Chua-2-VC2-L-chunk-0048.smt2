(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= 0. skoX)) (or (not (<= (* skoC (/ 76. 15.)) skoS)) (not (<= skoS (* skoC (/ 76. 15.)))))))
(set-info :status sat)
(check-sat)
