(set-logic QF_NRA)

(declare-fun skoCM1 () Real)
(declare-fun skoC () Real)
(declare-fun skoCP1 () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoCM1 (+ 12. (* skoCM1 (- 24.)))) 2.) (and (= (+ (- 1.) (* skoCP1 (* skoCP1 skoCP1))) skoX) (and (= (+ 1. (* skoCM1 (* skoCM1 skoCM1))) skoX) (and (= (* skoC (* skoC skoC)) skoX) (and (not (<= skoX 2.)) (and (not (<= skoCP1 0.)) (and (not (<= skoCM1 0.)) (and (not (<= skoC 0.)) (not (<= 10. skoX)))))))))))
(set-info :status sat)
(check-sat)
