(set-logic QF_NRA)

(declare-fun skoCM1 () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoCM1 (+ (- 12.) (* skoCM1 (+ 60. (* skoCM1 (- 120.)))))) (- 1.))) (and (not (<= skoX 1.)) (and (not (<= skoCM1 0.)) (not (<= skoC 0.))))))
(set-info :status sat)
(check-sat)
