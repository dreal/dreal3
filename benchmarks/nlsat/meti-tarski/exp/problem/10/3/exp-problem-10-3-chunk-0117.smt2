(set-logic QF_NRA)

(declare-fun skoCP1 () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoCP1 (+ (* skoCM1 (/ (- 1.) 550998028800.)) (* skoCP1 (+ (* skoCM1 (/ (- 1.) 20407334400.)) (* skoCP1 (+ (* skoCM1 (/ (- 181.) 183666009600.)) (* skoCP1 (+ (* skoCM1 (/ (- 1.) 62985600.)) (* skoCP1 (+ (* skoCM1 (/ (- 361.) 1700611200.)) (* skoCP1 (+ (* skoCM1 (/ (- 409.) 170061120.)) (* skoCP1 (+ (* skoCM1 (/ (- 49.) 2099520.)) (* skoCP1 (+ (* skoCM1 (/ (- 17.) 87480.)) (* skoCP1 (+ (* skoCM1 (/ (- 121.) 87480.)) (* skoCP1 (+ (* skoCM1 (/ (- 1.) 120.)) (* skoCP1 (+ (* skoCM1 (/ (- 1.) 24.)) (* skoCP1 (+ (* skoCM1 (/ (- 1.) 6.)) (* skoCP1 (+ (* skoCM1 (/ (- 1.) 2.)) (* skoCP1 (+ (* skoCM1 (- 1.)) (* skoCP1 (+ (- 1.) (* skoCM1 (/ (- 21.) 10.)))))))))))))))))))))))))))))))) (* skoCM1 (/ 1. 24794911296000.)))) (and (not (<= skoX 2.)) (and (not (<= skoCP1 0.)) (and (not (<= skoCM1 0.)) (and (not (<= skoC 0.)) (not (<= 10. skoX))))))))
(set-info :status unsat)
(check-sat)
