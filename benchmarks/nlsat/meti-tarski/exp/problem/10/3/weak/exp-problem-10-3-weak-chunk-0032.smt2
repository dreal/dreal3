(set-logic QF_NRA)

(declare-fun skoCM1 () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (= (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 skoCM1)))) 0.) (and (not (= (* skoCM1 (* skoCM1 (* skoCM1 skoCM1))) 0.)) (and (not (= (* skoCM1 (* skoCM1 skoCM1)) 0.)) (and (not (= (* skoCM1 skoCM1) 0.)) (and (not (= skoCM1 0.)) (and (= (+ 1. (* skoCM1 (* skoCM1 skoCM1))) skoX) (and (= (* skoC (* skoC skoC)) skoX) (and (not (<= skoX 1.)) (and (not (<= skoCM1 0.)) (not (<= skoC 0.))))))))))))
(set-info :status unsat)
(check-sat)
