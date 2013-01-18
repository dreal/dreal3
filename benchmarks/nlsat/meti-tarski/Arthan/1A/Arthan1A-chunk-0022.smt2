(set-logic QF_NRA)

(declare-fun skoCOSS () Real)
(declare-fun skoSINS () Real)
(declare-fun skoS () Real)
(declare-fun pi () Real)
(assert (and (not (= (* skoSINS skoSINS) (+ 1. (* skoCOSS (* skoCOSS (- 1.)))))) (and (not (<= (* pi (/ 1. 2.)) skoS)) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= 0. skoS) (and (<= 0. skoCOSS) (<= skoSINS skoS))))))))
(set-info :status sat)
(check-sat)
