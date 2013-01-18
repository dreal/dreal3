(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (* skoX (+ (/ (- 345344.) 175.) (* skoX (+ (/ (- 410096.) 21875.) (* skoX (+ (/ (- 973978.) 8203125.) (* skoX (+ (/ (- 9252791.) 18750000000.) (* skoX (+ (/ (- 175803029.) 131250000000000.) (* skoX (/ (- 3340257551.) 1575000000000000000.)))))))))))) (/ 710912. 7.))) (and (not (<= (* skoX (+ (/ 5472. 125.) (* skoX (+ (/ 6498. 15625.) (* skoX (+ (/ 20577. 7812500.) (* skoX (+ (/ 2736741. 250000000000.) (* skoX (+ (/ 7428297. 250000000000000.) (* skoX (/ 47045881. 1000000000000000000.)))))))))))) (- 2304.))) (and (not (<= skoS (* skoC (/ 1770. 689.)))) (and (or (not (<= (* skoC (/ 1770. 689.)) skoS)) (<= skoX 0.)) (and (or (<= skoS (* skoC (/ 1770. 689.))) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX)))))))))
(set-info :status unsat)
(check-sat)
