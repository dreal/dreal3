(set-logic QF_NRA)

(declare-fun skoB () Real)
(declare-fun skoT () Real)
(declare-fun skoA () Real)
(assert (and (not (<= 0. skoA)) (and (not (<= (* skoT (* skoT (* skoB (- 1.)))) (* skoB (* skoB skoB)))) (and (not (<= (* skoT (+ (* skoB (+ (* skoA (* skoA (- 1.))) (* skoB (+ (* skoA 2.) (* skoB (+ (- 1.) (* skoA (/ (- 3.) 10.)))))))) (* skoT (+ (* skoB (* skoA (/ (- 157.) 50.))) (* skoT (+ skoA (* skoB (+ (- 1.) (* skoA (/ (- 3.) 10.)))))))))) (* skoB (* skoB (* skoB (* skoA (/ 157. 50.))))))) (and (not (<= skoB (* skoA (- 1.)))) (and (not (<= skoT 1.)) (not (<= skoB skoA))))))))
(set-info :status unsat)
(check-sat)
