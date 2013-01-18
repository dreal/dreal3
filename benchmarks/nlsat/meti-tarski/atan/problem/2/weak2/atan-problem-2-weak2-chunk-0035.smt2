(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoA () Real)
(declare-fun skoT () Real)
(assert (and (<= 0. skoB) (and (not (<= skoT 0.)) (and (not (<= skoB (* skoA (- 1.)))) (and (not (<= skoT 1.)) (not (<= skoB skoA)))))))
(set-info :status sat)
(check-sat)
