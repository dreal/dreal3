(set-logic QF_NRA)

(declare-fun skoT () Real)
(declare-fun skoB () Real)
(declare-fun skoA () Real)
(assert (and (not (<= (* skoT (+ (* skoB (/ 157. 100.)) (* skoT (+ (- 1.) skoB)))) (* skoB skoA))) (and (not (<= (* skoT (+ (* skoB (* skoB (* skoB (* skoA (* skoA (/ (- 157.) 50.)))))) (* skoT (+ (* skoB (+ (* skoA (+ (- 1.) (* skoA (* skoA 2.)))) (* skoB (+ (+ 1. (* skoA (* skoA 2.))) (* skoB (+ (* skoA (+ 2. (* skoA (+ (- 2.) (* skoA (- 1.)))))) (* skoB (* skoA skoA)))))))) (* skoT (+ (* skoB (+ (* skoA (* skoA (/ (- 157.) 50.))) (* skoB (* skoB (/ (- 157.) 50.))))) (* skoT (+ (+ (* skoA (* skoA 2.)) (* skoB (+ (* skoA (+ 2. (* skoA (+ (- 2.) (* skoA (- 1.)))))) (* skoB (+ (+ 2. (* skoA skoA)) (* skoB (+ (+ (- 2.) (* skoA (- 1.))) skoB))))))) (* skoT (+ (* skoB (/ (- 157.) 50.)) (* skoT (+ 2. (* skoB (+ (+ (- 2.) (* skoA (- 1.))) skoB)))))))))))))) (* skoB (* skoB (* skoB (* skoA (* skoA (* skoA (- 2.))))))))) (and (not (<= skoT (/ 3. 2.))) (and (not (<= skoA 0.)) (and (not (<= 2. skoB)) (not (<= skoB skoA))))))))
(set-info :status sat)
(check-sat)

