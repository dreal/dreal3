(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSX () Real)
(declare-fun skoSMX () Real)
(assert (and (<= (* skoX (* skoX (- 1.))) (- 3.)) (and (<= (* skoX skoX) 1.) (and (= skoX (+ 1. (* skoSMX (* skoSMX (- 1.))))) (and (= (+ (- 1.) (* skoSX skoSX)) skoX) (and (<= skoX 1.) (and (<= 0. skoSX) (and (<= 0. skoSMX) (not (<= skoX 0.))))))))))
(set-info :status unsat)
(check-sat)
