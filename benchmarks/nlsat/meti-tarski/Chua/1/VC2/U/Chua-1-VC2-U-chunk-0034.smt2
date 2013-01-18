(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoC (/ 3. 13.)) skoS)) (and (not (<= (* skoX (+ (/ (- 25764.) 875.) (* skoX (/ (- 323817.) 3500000.)))) (/ 21528. 7.))) (and (not (<= (* skoX (+ (/ 57. 500.) (* skoX (/ 361. 1000000.)))) (- 12.))) (not (<= skoX 0.))))))
(set-info :status unsat)
(check-sat)
