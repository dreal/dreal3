(set-logic QF_NRA)

(declare-fun skoEC1 () Real)
(declare-fun skoXC1 () Real)
(declare-fun skoRC1 () Real)
(assert (and (not (<= (* skoXC1 (+ (/ 1. 2.) (* skoEC1 (+ (/ 3. 2.) (* skoEC1 (+ (/ 3. 2.) (* skoEC1 (/ 1. 2.)))))))) (* skoRC1 (* skoRC1 (+ (/ 1. 2.) (* skoEC1 (+ (- 1.) (* skoEC1 (/ (- 1.) 2.))))))))) (and (<= (* skoXC1 (* skoXC1 (/ (- 1.) 4.))) (+ 1. (* skoRC1 (- 1.)))) (and (<= (* skoXC1 (+ 1. (* skoXC1 (/ (- 1.) 4.)))) skoRC1) (and (<= skoEC1 (/ 1. 32.)) (and (<= (/ (- 1.) 32.) skoEC1) (and (<= skoXC1 2.) (and (<= skoRC1 3.) (and (<= (/ 1. 2.) skoXC1) (<= 0. skoRC1))))))))))
(set-info :status sat)
(check-sat)
