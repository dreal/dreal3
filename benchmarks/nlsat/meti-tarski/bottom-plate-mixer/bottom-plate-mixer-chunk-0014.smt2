(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (/ 177. 366500000.) skoX)) (not (<= skoS (+ (/ 760000. 7383.) (* skoC (/ (- 3400.) 7383.)))))))
(set-info :status sat)
(check-sat)
