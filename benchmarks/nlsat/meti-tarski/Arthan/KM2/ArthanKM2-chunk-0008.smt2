(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoSINS () Real)
(declare-fun skoCOSS () Real)
(assert (and (= (* skoSINS skoSINS) (+ 1. (* skoCOSS (* skoCOSS (- 1.))))) (and (<= (* skoSINS (+ (+ (+ (/ (- 5.) 2.) (* skoCOSS (/ (- 1.) 2.))) (* skoS (+ (/ (- 3.) 2.) (* skoS (+ (/ 3. 2.) (* skoS (/ 1. 2.))))))) (* skoSINS (+ (/ 1. 4.) (* skoS (/ 1. 4.)))))) (+ (+ (- 2.) (* skoCOSS (+ (- 3.) (* skoCOSS (/ (- 1.) 2.))))) (* skoS (+ (+ (- 6.) (* skoCOSS (+ (- 6.) (* skoCOSS (/ (- 1.) 2.))))) (* skoS (+ (+ (- 6.) (* skoCOSS (- 3.))) (* skoS (- 2.)))))))) (<= (/ 9. 20.) skoS))))
(set-info :status unsat)
(check-sat)

