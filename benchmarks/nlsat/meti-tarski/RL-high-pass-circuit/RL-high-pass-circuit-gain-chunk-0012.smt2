(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ 6000. (* skoX 1000000.))) (- 12.))) (and (not (<= (* skoX (+ (+ (+ (/ (- 6114000.) 19.) (* skoC (/ 4500000. 19.))) (* skoS (/ (- 9300000.) 247.))) (* skoX (+ (+ (/ (- 981000000.) 19.) (* skoC (/ 750000000. 19.))) (* skoS (/ (- 1550000000.) 247.)))))) (+ (+ (/ 11772. 19.) (* skoC (/ (- 9000.) 19.))) (* skoS (/ 18600. 247.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX (/ 4. 5.)) (<= (/ 1. 500.) skoX))))))
(set-info :status unsat)
(check-sat)
