(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (* skoX (+ (/ (- 57.) 500.) (* skoX (/ (- 361.) 1000000.)))) 12.)) (and (not (<= skoS (* skoC (/ (- 235.) 42.)))) (not (<= skoX 0.)))))
(set-info :status unsat)
(check-sat)
