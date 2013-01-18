(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(declare-fun skoVF () Real)
(assert (and (<= (* skoT (+ (/ 477. 250.) (* skoT (/ 25281. 250000.)))) (- 12.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (not (<= skoVF 0.)) (and (not (<= skoT 0.)) (not (<= (/ 151. 50.) skoVF)))))))
(set-info :status unsat)
(check-sat)
