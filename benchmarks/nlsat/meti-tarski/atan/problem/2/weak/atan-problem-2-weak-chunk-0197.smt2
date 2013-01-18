(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoT () Real)
(declare-fun skoA () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (* skoT (+ (* skoS (* skoB (/ (- 157.) 100.))) (* skoT (+ (* skoB (+ skoA (* skoB (- 1.)))) (* skoS (+ (- 1.) skoB)))))) (* skoS (* skoB skoA)))) (and (not (<= skoA 0.)) (and (or (not (<= 0. skoT)) (not (<= skoT 1.))) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA))))))))
(set-info :status sat)
(check-sat)
