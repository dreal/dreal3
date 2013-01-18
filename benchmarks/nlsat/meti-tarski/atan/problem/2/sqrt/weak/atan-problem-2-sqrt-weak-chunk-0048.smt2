(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoT () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (* skoT (* skoT (* skoB (+ (* skoA (- 1.)) skoB)))) 0.)) (and (not (<= skoB skoA)) (and (not (<= 2. skoB)) (and (not (<= skoA 0.)) (not (<= skoT (/ 3. 2.))))))))
(set-info :status sat)
(check-sat)
