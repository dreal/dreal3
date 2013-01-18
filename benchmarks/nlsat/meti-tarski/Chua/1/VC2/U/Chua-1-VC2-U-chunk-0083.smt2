(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoC (/ 3. 13.)) skoS)) (and (not (<= (* skoX (+ (/ (- 9855072.) 875.) (* skoX (+ (/ (- 11702898.) 109375.) (* skoX (+ (/ (- 37059177.) 54687500.) (* skoX (+ (/ (- 704124363.) 250000000000.) (* skoX (+ (/ (- 13378362897.) 1750000000000000.) (* skoX (/ (- 84729631681.) 7000000000000000000.)))))))))))) (/ 4133376. 7.))) (and (not (<= (* skoX (+ (/ 5472. 125.) (* skoX (+ (/ 6498. 15625.) (* skoX (+ (/ 20577. 7812500.) (* skoX (+ (/ 2736741. 250000000000.) (* skoX (+ (/ 7428297. 250000000000000.) (* skoX (/ 47045881. 1000000000000000000.)))))))))))) (- 2304.))) (and (or (not (<= skoS (* skoC (/ 3. 13.)))) (<= skoX 0.)) (and (or (<= (* skoC (/ 3. 13.)) skoS) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX)))))))))
(set-info :status unsat)
(check-sat)
