(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoX (+ (/ (- 567.) 6250000.) (* skoX (/ 567. 156250000000.)))) (/ (- 189.) 250.)) (and (<= (* skoX (+ (/ 567. 6250000.) (* skoX (/ (- 567.) 156250000000.)))) (/ 189. 250.)) (and (<= (* skoX (+ (+ (+ (/ (- 639.) 156250.) (* skoC (/ (- 1593.) 625000.))) (* skoS (/ 6201. 6250000.))) (* skoX (+ (+ (/ 639. 3906250000.) (* skoC (/ (- 1593.) 15625000000.))) (* skoS (/ 6201. 156250000000.)))))) (+ (+ (/ (- 852.) 25.) (* skoC (/ 531. 25.))) (* skoS (/ (- 2067.) 250.)))) (and (not (<= skoS (* skoC (/ 1770. 689.)))) (and (or (not (<= (* skoC (/ 1770. 689.)) skoS)) (<= skoX 0.)) (and (or (<= skoS (* skoC (/ 1770. 689.))) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX))))))))))
(set-info :status unsat)
(check-sat)
