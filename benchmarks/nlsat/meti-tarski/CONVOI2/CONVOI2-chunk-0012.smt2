(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoVF () Real)
(declare-fun skoT () Real)
(assert (and (<= (- 5.) skoVF) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (not (<= skoVF 0.)) (and (not (<= skoT 0.)) (not (<= (/ 151. 50.) skoVF)))))))
(set-info :status sat)
(check-sat)
