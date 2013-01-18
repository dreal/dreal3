(set-logic QF_NRA)

(declare-fun skoA () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= 0. skoA) (and (<= (* skoA (+ 1. (* skoA (* skoA (/ (- 1.) 6.))))) 0.) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= (* pi (/ 1. 2.)) skoA)) (and (not (<= skoX 0.)) (not (<= skoA skoX)))))))))
(set-info :status unsat)
(check-sat)
