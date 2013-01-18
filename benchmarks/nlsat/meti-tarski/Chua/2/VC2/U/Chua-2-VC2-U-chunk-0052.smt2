(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ (- 16128.) 5.) (* skoX (+ (/ 28224. 625.) (* skoX (+ (/ (- 32928.) 78125.) (* skoX (+ (/ 50421. 19531250.) (* skoX (+ (/ (- 50421.) 4882812500.) (* skoX (/ 117649. 4882812500000.)))))))))))) (- 112896.)) (and (not (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX))))))
(set-info :status unsat)
(check-sat)
