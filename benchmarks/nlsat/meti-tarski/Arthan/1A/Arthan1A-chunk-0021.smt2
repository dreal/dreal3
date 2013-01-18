(set-logic QF_NRA)

(declare-fun skoCOSS () Real)
(declare-fun skoSINS () Real)
(declare-fun pi () Real)
(declare-fun skoS () Real)
(assert (and (not (= (* skoSINS skoSINS) (+ 1. (* skoCOSS (* skoCOSS (- 1.)))))) (and (not (<= (* pi (/ 1. 2.)) skoS)) (and (not (<= pi (/ 15707963. 5000000.))) (not (<= (/ 31415927. 10000000.) pi))))))
(set-info :status sat)
(check-sat)
