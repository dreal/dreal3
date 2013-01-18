(set-logic QF_NRA)

(declare-fun skoXC1 () Real)
(declare-fun skoRC1 () Real)
(declare-fun skoEC1 () Real)
(assert (and (<= (* skoXC1 (+ 1. (* skoXC1 (/ (- 1.) 4.)))) skoRC1) (and (<= skoEC1 (/ 1. 32.)) (and (<= (/ (- 1.) 32.) skoEC1) (and (<= skoXC1 2.) (and (<= skoRC1 3.) (and (<= (/ 1. 2.) skoXC1) (<= 0. skoRC1))))))))
(set-info :status sat)
(check-sat)
