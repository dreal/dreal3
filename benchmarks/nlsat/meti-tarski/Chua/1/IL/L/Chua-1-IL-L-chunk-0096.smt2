(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ 3841344. 575.) (* skoX (+ (/ 4561596. 71875.) (* skoX (+ (/ 7222527. 17968750.) (* skoX (+ (/ 960596091. 575000000000.) (* skoX (+ (/ 2607332247. 575000000000000.) (* skoX (/ 16513104231. 2300000000000000000.)))))))))))) (/ (- 8034048.) 23.)) (and (<= skoS (* skoC (/ (- 235.) 42.))) (and (<= (* skoC (/ (- 235.) 42.)) skoS) (and (or (not (<= skoS (* skoC (/ (- 235.) 42.)))) (<= skoX 0.)) (and (or (<= (* skoC (/ (- 235.) 42.)) skoS) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX)))))))))
(set-info :status unsat)
(check-sat)
