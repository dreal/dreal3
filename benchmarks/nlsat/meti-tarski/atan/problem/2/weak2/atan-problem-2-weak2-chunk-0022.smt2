(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (<= (* skoT (+ (* skoB (* skoB (- 1.))) (* skoT (* skoT (- 1.))))) 0.) (and (<= (* skoT (+ (* skoB skoB) (* skoT skoT))) 0.) (and (not (<= (* skoT (* skoT (+ (+ (* skoA (- 1.)) (* skoB (* skoB (/ (- 3.) 10.)))) (* skoT (* skoT (/ (- 3.) 10.)))))) (* skoB (* skoB skoB)))) (and (not (<= skoB (* skoA (- 1.)))) (and (not (<= skoT 1.)) (not (<= skoB skoA))))))))
(set-info :status unsat)
(check-sat)
