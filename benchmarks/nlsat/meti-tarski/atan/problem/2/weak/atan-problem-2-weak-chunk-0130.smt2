(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoS () Real)
(declare-fun skoT () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (* skoS skoB) 0.)) (and (not (<= skoT 0.)) (and (or (not (<= 0. skoT)) (not (<= skoT 1.))) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA))))))))
(set-info :status sat)
(check-sat)
