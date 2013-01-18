(set-logic QF_NRA)

(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(assert (and (not (= (+ 1. (* skoCM1 (* skoCM1 skoCM1))) skoX)) (and (not (<= skoX 1.)) (and (not (<= skoCM1 0.)) (not (<= skoC 0.))))))
(set-info :status sat)
(check-sat)
