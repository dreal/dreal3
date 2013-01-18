(set-logic QF_NRA)

(declare-fun skoCM1 () Real)
(declare-fun skoCP1 () Real)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoCP1 (+ (/ 1. 10.) (* skoCM1 (+ (/ (- 126.) 5.) (* skoCM1 (+ 6. (* skoCM1 (- 252.)))))))) (+ (- 1.) (* skoCM1 (+ 12. (* skoCM1 (+ (- 60.) (* skoCM1 120.)))))))) (and (not (<= skoX 2.)) (and (not (<= skoCP1 0.)) (and (not (<= skoCM1 0.)) (and (not (<= skoC 0.)) (not (<= 10. skoX))))))))
(set-info :status sat)
(check-sat)
