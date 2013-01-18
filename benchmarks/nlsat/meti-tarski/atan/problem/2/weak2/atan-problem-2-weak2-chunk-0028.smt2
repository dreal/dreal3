(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (* skoT (* skoT (+ (* skoB (* skoB (/ (- 3.) 10.))) (* skoT (* skoT (/ (- 3.) 10.)))))) (* skoB (* skoB (+ (* skoA (- 1.)) skoB))))) (and (not (<= (* skoT (+ (* skoB skoB) (* skoT skoT))) 0.)) (and (not (= skoT 0.)) (and (not (<= skoB (* skoA (- 1.)))) (and (not (<= skoT 1.)) (not (<= skoB skoA))))))))
(set-info :status unsat)
(check-sat)
