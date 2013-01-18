(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoC (/ (- 235.) 42.)) skoS)) (and (not (<= (* skoX (+ (/ (- 201381.) 11500.) (* skoX (/ (- 1258807.) 23000000.)))) (/ 41844. 23.))) (and (not (<= (* skoX (+ (/ 57. 500.) (* skoX (/ 361. 1000000.)))) (- 12.))) (not (<= skoX 0.))))))
(set-info :status unsat)
(check-sat)
