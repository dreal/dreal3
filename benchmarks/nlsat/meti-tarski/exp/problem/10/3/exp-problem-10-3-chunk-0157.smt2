(set-logic QF_NRA)

(declare-fun skoCM1 () Real)
(declare-fun skoCP1 () Real)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoCP1 (+ (+ (/ 3. 5.) (* skoCM1 (+ (/ 342. 5.) (* skoCM1 (/ 36. 5.))))) (* skoCP1 (+ (/ (- 126.) 5.) (* skoCM1 (+ (/ 36. 5.) (* skoCM1 (/ (- 1512.) 5.)))))))) (+ (/ 21. 10.) (* skoCM1 (+ (/ (- 3.) 5.) (* skoCM1 (/ 126. 5.))))))) (and (not (<= skoX 2.)) (and (not (<= skoCP1 0.)) (and (not (<= skoCM1 0.)) (and (not (<= skoC 0.)) (not (<= 10. skoX))))))))
(set-info :status unsat)
(check-sat)
