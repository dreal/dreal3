(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (/ 177. 366500000.) skoX)) (not (<= (+ (/ 760000. 7383.) (* skoC (/ (- 3400.) 7383.))) skoS))))
(set-info :status sat)
(check-sat)
