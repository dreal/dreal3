(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoX () Real)
(assert (and (not (<= skoX 0.)) (not (<= skoS (* skoC (/ (- 235.) 42.))))))
(set-info :status sat)
(check-sat)
