(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoVF () Real)
(assert (and (<= (* skoVF (+ (/ (- 93.) 25.) (* skoT (+ (/ 110187. 25000.) (* skoT (/ (- 783711.) 25000000.)))))) (+ (/ (- 207.) 5.) (* skoT (+ (/ (- 157887.) 5000.) (* skoT (/ (- 1744389.) 5000000.)))))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (not (<= skoVF 0.)) (and (not (<= skoT 0.)) (not (<= (/ 151. 50.) skoVF)))))))
(set-info :status unsat)
(check-sat)
