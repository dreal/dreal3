(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoX (+ (/ (- 693.) 62500000.) (* skoX (/ 693. 1562500000000.)))) (/ (- 231.) 2500.)) (and (<= (* skoX (+ (/ 693. 62500000.) (* skoX (/ (- 693.) 1562500000000.)))) (/ 231. 2500.)) (and (<= (* skoX (+ (+ (+ (/ (- 178299.) 62500000.) (* skoC (/ 1647. 6250000.))) (* skoS (/ (- 7137.) 6250000.))) (* skoX (+ (+ (/ 178299. 1562500000000.) (* skoC (/ 1647. 156250000000.))) (* skoS (/ (- 7137.) 156250000000.)))))) (+ (+ (/ (- 59433.) 2500.) (* skoC (/ (- 549.) 250.))) (* skoS (/ 2379. 250.)))) (and (not (<= (* skoC (/ 3. 13.)) skoS)) (and (or (not (<= skoS (* skoC (/ 3. 13.)))) (<= skoX 0.)) (and (or (<= (* skoC (/ 3. 13.)) skoS) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX))))))))))
(set-info :status unsat)
(check-sat)
