(set-logic QF_NRA)

(declare-fun skoCP1 () Real)
(declare-fun skoC () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(assert (and (not (<= skoCP1 0.)) (and (= (+ (- 1.) (* skoCP1 (* skoCP1 skoCP1))) skoX) (and (= (+ 1. (* skoCM1 (* skoCM1 skoCM1))) skoX) (and (= (* skoC (* skoC skoC)) skoX) (and (<= 0. skoCP1) (and (<= 0. skoCM1) (and (<= 0. skoC) (not (<= skoX (/ 7. 5.)))))))))))
(set-info :status sat)
(check-sat)
