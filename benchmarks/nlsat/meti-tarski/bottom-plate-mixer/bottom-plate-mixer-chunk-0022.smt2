(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoCB () Real)
(declare-fun skoC () Real)
(declare-fun skoSB () Real)
(assert (not (<= skoSB (+ (+ (+ (/ 12695. 52.) (* skoC (/ (- 570.) 13.))) (* skoCB (/ (- 49.) 65.))) (* skoS (- 200.))))))
(set-info :status sat)
(check-sat)
