(set-logic QF_NRA)

(declare-fun skoS () Real)
(declare-fun skoSINS () Real)
(declare-fun skoCOSS () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoSINS (+ (+ (+ (- 3.) (* skoCOSS (- 2.))) (* skoS (+ (- 4.) (* skoS (+ 2. skoS))))) (* skoSINS (+ 1. skoS)))) (+ (+ 2. (* skoCOSS (+ (- 2.) (* skoCOSS (- 2.))))) (* skoS (+ (* skoCOSS (+ (- 10.) (* skoCOSS (- 2.)))) (* skoS (+ (+ (- 6.) (* skoCOSS (- 6.))) (* skoS (- 2.)))))))) (and (not (<= (* pi (/ 1. 2.)) skoS)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= 0. skoS) (and (<= 0. skoCOSS) (<= skoSINS skoS))))))))
(set-info :status sat)
(check-sat)
