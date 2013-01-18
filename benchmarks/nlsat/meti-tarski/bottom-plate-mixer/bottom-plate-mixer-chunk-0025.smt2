(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (/ 177. 366500000.) skoX) (and (<= skoX (/ 177. 366500000.)) (and (not (<= skoS (+ (/ 760000. 7383.) (* skoC (/ (- 3400.) 7383.))))) (and (<= skoX (/ 1. 10000000.)) (<= 0. skoX))))))
(set-info :status unsat)
(check-sat)
