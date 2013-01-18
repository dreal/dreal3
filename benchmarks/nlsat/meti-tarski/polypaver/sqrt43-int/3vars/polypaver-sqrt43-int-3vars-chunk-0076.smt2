(set-logic QF_NRA)

(declare-fun skoEC1 () Real)
(declare-fun skoRC1 () Real)
(declare-fun skoXC1 () Real)
(assert (not (<= (* skoXC1 (+ (/ 1. 2.) (* skoEC1 (+ (/ 3. 2.) (* skoEC1 (+ (/ 3. 2.) (* skoEC1 (/ 1. 2.)))))))) (* skoRC1 (* skoRC1 (+ (/ 1. 2.) (* skoEC1 (+ (- 1.) (* skoEC1 (/ (- 1.) 2.))))))))))
(set-info :status sat)
(check-sat)
