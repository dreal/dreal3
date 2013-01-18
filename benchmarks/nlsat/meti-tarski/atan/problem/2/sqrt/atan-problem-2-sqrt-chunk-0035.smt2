(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (<= (* skoT (* skoT (+ skoA (* skoB (- 1.))))) 0.) (and (not (<= skoB skoA)) (and (not (<= 2. skoB)) (and (not (<= skoA 0.)) (and (not (= skoT 0.)) (<= 0. skoT)))))))
(set-info :status sat)
(check-sat)
