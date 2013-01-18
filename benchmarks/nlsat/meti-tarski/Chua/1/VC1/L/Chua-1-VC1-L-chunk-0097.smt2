(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoC (/ 1770. 689.)) skoS) (and (<= (* skoX (+ (/ 345344. 175.) (* skoX (+ (/ 410096. 21875.) (* skoX (+ (/ 973978. 8203125.) (* skoX (+ (/ 9252791. 18750000000.) (* skoX (+ (/ 175803029. 131250000000000.) (* skoX (/ 3340257551. 1575000000000000000.)))))))))))) (/ (- 710912.) 7.)) (and (<= skoS (* skoC (/ 1770. 689.))) (and (or (not (<= (* skoC (/ 1770. 689.)) skoS)) (<= skoX 0.)) (and (or (<= skoS (* skoC (/ 1770. 689.))) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX)))))))))
(set-info :status unsat)
(check-sat)
