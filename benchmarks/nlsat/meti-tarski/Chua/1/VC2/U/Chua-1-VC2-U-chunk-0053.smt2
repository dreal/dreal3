(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ (- 57.) 500.) (* skoX (/ (- 361.) 1000000.)))) 12.) (and (or (not (<= skoS (* skoC (/ 3. 13.)))) (<= skoX 0.)) (and (or (<= (* skoC (/ 3. 13.)) skoS) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX)))))))
(set-info :status sat)
(check-sat)
