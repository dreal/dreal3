(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoC (/ 86400000. 2025130727.)) skoS)) (and (not (<= (* skoX (+ (+ (+ (/ 23. 13.) (* skoC (/ (- 621.) 8125.))) (* skoS (/ 46578006721. 26000000000.))) (* skoX (+ (+ (/ 529. 312000.) (* skoC (/ 4761. 65000000.))) (* skoS (/ (- 1071294154583.) 624000000000000.)))))) (+ (+ (/ (- 8000.) 13.) (* skoC (/ (- 1728.) 65.))) (* skoS (/ 2025130727. 3250000.))))) (and (not (<= skoX 0.)) (and (<= (* skoC (/ 86400000. 2025130727.)) skoS) (and (or (not (<= (* skoC (/ 86400000. 2025130727.)) skoS)) (not (<= skoS (* skoC (/ 86400000. 2025130727.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX)))))))))
(set-info :status unsat)
(check-sat)
