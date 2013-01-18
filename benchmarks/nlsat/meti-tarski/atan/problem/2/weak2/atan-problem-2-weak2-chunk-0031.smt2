(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoA () Real)
(declare-fun skoB () Real)
(assert (and (<= 0. skoT) (and (not (= skoT 0.)) (and (not (<= skoB (* skoA (- 1.)))) (and (not (<= skoT 1.)) (not (<= skoB skoA)))))))
(set-info :status sat)
(check-sat)
