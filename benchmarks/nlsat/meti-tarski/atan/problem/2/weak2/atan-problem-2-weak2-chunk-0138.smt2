(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (not (<= 0. skoA)) (and (not (<= (* skoT (* skoT skoB)) (* skoB (* skoB (* skoB (- 1.)))))) (and (not (<= (* skoT (+ (* skoB (+ (* skoA skoA) (* skoB (+ (* skoA (- 2.)) (* skoB (+ 1. (* skoA (/ 3. 10.)))))))) (* skoT (+ (* skoB (* skoA (/ 157. 50.))) (* skoT (+ (* skoA (- 1.)) (* skoB (+ 1. (* skoA (/ 3. 10.)))))))))) (* skoB (* skoB (* skoB (* skoA (/ (- 157.) 50.))))))) (and (or (not (<= 0. skoA)) (or (not (<= (* skoT (+ (* skoB (* skoB (* skoB (/ (- 157.) 100.)))) (* skoT (+ (* skoB (* skoB (+ 2. (* skoB (/ (- 3.) 10.))))) (* skoT (+ (* skoB (/ (- 157.) 100.)) (* skoT (+ 1. (* skoB (/ (- 3.) 10.)))))))))) (* skoB (* skoB (* skoB (* skoA (- 1.))))))) (<= skoB skoT))) (and (not (<= skoB (* skoA (- 1.)))) (and (not (<= skoT 1.)) (not (<= skoB skoA)))))))))
(set-info :status sat)
(check-sat)

