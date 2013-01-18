(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ 9855072. 875.) (* skoX (+ (/ 11702898. 109375.) (* skoX (+ (/ 37059177. 54687500.) (* skoX (+ (/ 704124363. 250000000000.) (* skoX (+ (/ 13378362897. 1750000000000000.) (* skoX (/ 84729631681. 7000000000000000000.)))))))))))) (/ (- 4133376.) 7.)) (and (<= skoS (* skoC (/ 3. 13.))) (and (<= (* skoC (/ 3. 13.)) skoS) (and (or (not (<= skoS (* skoC (/ 3. 13.)))) (<= skoX 0.)) (and (or (<= (* skoC (/ 3. 13.)) skoS) (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 289.) (<= 0. skoX)))))))))
(set-info :status unsat)
(check-sat)
