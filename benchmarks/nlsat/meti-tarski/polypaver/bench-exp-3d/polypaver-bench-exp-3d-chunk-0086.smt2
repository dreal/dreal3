(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoZ (+ 332640. (* skoZ (+ (- 75600.) (* skoZ (+ 10080. (* skoZ (+ (- 840.) (* skoZ (+ 42. (* skoZ (- 1.)))))))))))) 665280.) (and (<= 0. skoX) (and (<= 0. skoY) (and (<= 0. skoZ) (and (<= skoX 1.) (and (<= skoY 1.) (and (<= skoZ 1.) (and (<= skoZ (+ (+ 2. (* skoX (- 1.))) (* skoY (- 1.)))) (<= (+ (+ 2. (* skoX (- 1.))) (* skoY (- 1.))) skoZ))))))))))
(set-info :status sat)
(check-sat)
