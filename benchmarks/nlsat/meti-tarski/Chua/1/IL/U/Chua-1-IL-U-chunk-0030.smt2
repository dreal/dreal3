(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= 0. skoX)) (or (not (<= (* skoC (/ (- 235.) 42.)) skoS)) (not (<= skoS (* skoC (/ (- 235.) 42.)))))))
(set-info :status sat)
(check-sat)
