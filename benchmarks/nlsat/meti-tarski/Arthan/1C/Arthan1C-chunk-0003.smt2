(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoSINS () Real)
(declare-fun skoCOSS () Real)
(assert (not (<= (* skoSINS (+ (+ (+ (- 3.) (* skoCOSS (- 2.))) (* skoS (+ (- 4.) (* skoS (+ 2. skoS))))) (* skoSINS (+ 1. skoS)))) (+ (+ 2. (* skoCOSS (+ (- 2.) (* skoCOSS (- 2.))))) (* skoS (+ (* skoCOSS (+ (- 10.) (* skoCOSS (- 2.)))) (* skoS (+ (+ (- 6.) (* skoCOSS (- 6.))) (* skoS (- 2.))))))))))
(set-info :status sat)
(check-sat)
