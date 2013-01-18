(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoA () Real)
(declare-fun skoT () Real)
(assert (and (<= (* skoT (+ skoA (* skoB (+ (- 1.) (* skoA (- 1.)))))) (* skoB (* skoA (/ 157. 50.)))) (and (not (<= skoT (/ 3. 2.))) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA)))))))
(set-info :status sat)
(check-sat)
