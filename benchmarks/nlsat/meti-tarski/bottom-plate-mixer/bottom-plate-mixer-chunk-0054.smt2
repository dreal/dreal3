(set-logic QF_NRA)

(declare-fun skoSB () Real)
(declare-fun skoS () Real)
(declare-fun skoCB () Real)
(declare-fun skoC () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (+ (+ (+ (/ 12695. 52.) (* skoC (/ (- 570.) 13.))) (* skoCB (/ (- 49.) 65.))) (* skoS (- 200.))) skoSB)) (and (not (<= skoX (/ 177. 366500000.))) (and (= (* skoSB skoSB) (+ 1. (* skoCB (* skoCB (- 1.))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX (/ 1. 10000000.)) (<= 0. skoX)))))))
(set-info :status unsat)
(check-sat)

