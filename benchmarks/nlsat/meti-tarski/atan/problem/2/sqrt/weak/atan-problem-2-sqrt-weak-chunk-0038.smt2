(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (* skoT (* skoT (+ (+ (* skoA skoA) (* skoB skoB)) (* skoT skoT)))) (* skoB (* skoB (* skoA (* skoA (- 1.))))))) (and (not (<= skoB skoA)) (and (not (<= 2. skoB)) (and (not (<= skoA 0.)) (not (<= skoT (/ 3. 2.))))))))
(set-info :status sat)
(check-sat)
