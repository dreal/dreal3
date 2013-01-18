(set-logic QF_NRA)

(declare-fun skoCM1 () Real)
(declare-fun skoCP1 () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoCP1 (+ (+ (- 12.) (* skoCM1 (+ 72. (* skoCM1 (- 144.))))) (* skoCP1 (+ 24. (* skoCM1 (+ (- 144.) (* skoCM1 288.))))))) (+ (- 2.) (* skoCM1 (+ 12. (* skoCM1 (- 24.)))))) (and (= (+ (- 1.) (* skoCP1 (* skoCP1 skoCP1))) skoX) (and (= (+ 1. (* skoCM1 (* skoCM1 skoCM1))) skoX) (and (= (* skoC (* skoC skoC)) skoX) (and (not (<= skoX 2.)) (and (not (<= skoCP1 0.)) (and (not (<= skoCM1 0.)) (and (not (<= skoC 0.)) (not (<= 10. skoX)))))))))))
(set-info :status unsat)
(check-sat)
