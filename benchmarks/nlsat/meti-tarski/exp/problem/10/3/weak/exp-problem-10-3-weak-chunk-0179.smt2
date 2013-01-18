(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(assert (and (= (* skoC (* skoC (* skoC skoC))) 0.) (and (not (<= (* skoCM1 (+ 12. (* skoCM1 (+ (- 60.) (* skoCM1 120.))))) 1.)) (and (not (= (* skoC (* skoC skoC)) 0.)) (and (not (= (* skoC skoC) 0.)) (and (not (= skoC 0.)) (and (= (+ 1. (* skoCM1 (* skoCM1 skoCM1))) skoX) (and (= (* skoC (* skoC skoC)) skoX) (and (not (<= skoX 1.)) (and (not (<= skoCM1 0.)) (not (<= skoC 0.))))))))))))
(set-info :status unsat)
(check-sat)
