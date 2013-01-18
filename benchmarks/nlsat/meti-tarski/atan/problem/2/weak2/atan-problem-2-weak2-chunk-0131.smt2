(set-logic QF_NRA)

(declare-fun skoA () Real)
(declare-fun skoB () Real)
(declare-fun skoT () Real)
(assert (and (not (<= (* skoA (- 1.)) skoT)) (and (not (<= skoA 0.)) (and (not (<= skoB skoT)) (and (not (<= skoB (* skoA (- 1.)))) (and (not (<= skoT 1.)) (not (<= skoB skoA))))))))
(set-info :status unsat)
(check-sat)
