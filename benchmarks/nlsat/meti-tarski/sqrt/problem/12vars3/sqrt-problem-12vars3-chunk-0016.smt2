(set-logic QF_NRA)

(declare-fun skoSMX () Real)
(declare-fun skoSX () Real)
(declare-fun skoX () Real)
(assert (and (<= skoSX (+ (- 4.) (* skoSMX (- 1.)))) (and (= skoX (+ 1. (* skoSMX (* skoSMX (- 1.))))) (and (= (+ (- 1.) (* skoSX skoSX)) skoX) (and (<= skoX 1.) (and (<= 0. skoSX) (and (<= 0. skoSMX) (not (<= skoX 0.)))))))))
(set-info :status unsat)
(check-sat)
