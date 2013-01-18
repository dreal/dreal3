(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (<= (* skoX (+ (/ (- 69.) 2000.) (* skoX (/ (- 529.) 16000000.)))) 12.) (and (not (<= skoX 0.)) (and (<= (* skoC (/ 86400000. 2025130727.)) skoS) (and (or (not (<= (* skoC (/ 86400000. 2025130727.)) skoS)) (not (<= skoS (* skoC (/ 86400000. 2025130727.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX))))))))
(set-info :status sat)
(check-sat)
