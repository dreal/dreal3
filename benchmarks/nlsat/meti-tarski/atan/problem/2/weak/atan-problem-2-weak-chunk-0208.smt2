(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoT (+ (* skoS (* skoB (/ (- 157.) 100.))) (* skoT (+ (* skoB (+ skoA (* skoB (- 1.)))) (* skoS (+ (- 1.) skoB)))))) (* skoS (* skoB skoA))) (and (not (<= 0. skoT)) (and (or (<= 0. skoT) (<= skoT (* skoB (- 1.)))) (and (or (<= skoB skoT) (<= skoT 0.)) (and (or (not (<= (- 1.) skoT)) (<= 0. skoT)) (and (or (not (<= 0. skoT)) (not (<= skoT 1.))) (and (= (* skoT (* skoT (+ (+ (* skoA (* skoA (- 1.))) (* skoB (* skoB (- 1.)))) (* skoT (* skoT (- 1.)))))) (+ (* skoB (* skoB (* skoA skoA))) (* skoS (* skoS (- 1.))))) (and (<= 0. skoS) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA)))))))))))))
(set-info :status sat)
(check-sat)
