(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (* skoX (+ (/ (- 5472.) 125.) (* skoX (+ (/ (- 6498.) 15625.) (* skoX (+ (/ (- 20577.) 7812500.) (* skoX (+ (/ (- 2736741.) 250000000000.) (* skoX (+ (/ (- 7428297.) 250000000000000.) (* skoX (/ (- 47045881.) 1000000000000000000.)))))))))))) 2304.)) (and (not (<= skoX 0.)) (not (<= skoS (* skoC (/ 3. 13.)))))))
(set-info :status unsat)
(check-sat)
