(set-logic QF_NRA)

(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoCP1 () Real)
(assert (and (not (<= (* skoCM1 (+ (- 12.) (* skoCM1 (+ 60. (* skoCM1 (- 120.)))))) (- 1.))) (and (not (<= skoX 2.)) (and (not (<= skoCP1 0.)) (and (not (<= skoCM1 0.)) (and (not (<= skoC 0.)) (not (<= 10. skoX))))))))
(set-info :status sat)
(check-sat)
