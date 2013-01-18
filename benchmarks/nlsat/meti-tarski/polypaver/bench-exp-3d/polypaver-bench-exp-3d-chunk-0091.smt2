(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun skoZ () Real)
(assert (and (<= (* skoZ (+ (+ (+ 15120. (* skoX (+ (- 6720.) (* skoX (+ 1260. (* skoX (+ (- 120.) (* skoX 5.)))))))) (* skoY (+ (+ (- 6720.) (* skoX (+ 2520. (* skoX (+ (- 360.) (* skoX 20.)))))) (* skoY (+ (+ 1260. (* skoX (+ (- 360.) (* skoX 30.)))) (* skoY (+ (+ (- 120.) (* skoX 20.)) (* skoY 5.)))))))) (* skoZ (+ (+ (+ (- 3360.) (* skoX (+ 1260. (* skoX (+ (- 180.) (* skoX 10.)))))) (* skoY (+ (+ 1260. (* skoX (+ (- 360.) (* skoX 30.)))) (* skoY (+ (+ (- 180.) (* skoX 30.)) (* skoY 10.)))))) (* skoZ (+ (+ (+ 420. (* skoX (+ (- 120.) (* skoX 10.)))) (* skoY (+ (+ (- 120.) (* skoX 20.)) (* skoY 10.)))) (* skoZ (+ (+ (+ (- 30.) (* skoX 5.)) (* skoY 5.)) skoZ)))))))) (+ (+ 30240. (* skoX (+ (- 15120.) (* skoX (+ 3360. (* skoX (+ (- 420.) (* skoX (+ 30. (* skoX (- 1.))))))))))) (* skoY (+ (+ (- 15120.) (* skoX (+ 6720. (* skoX (+ (- 1260.) (* skoX (+ 120. (* skoX (- 5.))))))))) (* skoY (+ (+ 3360. (* skoX (+ (- 1260.) (* skoX (+ 180. (* skoX (- 10.))))))) (* skoY (+ (+ (- 420.) (* skoX (+ 120. (* skoX (- 10.))))) (* skoY (+ (+ 30. (* skoX (- 5.))) (* skoY (- 1.)))))))))))) (and (<= 0. skoX) (and (<= 0. skoY) (and (<= 0. skoZ) (and (<= skoX 1.) (and (<= skoY 1.) (and (<= skoZ 1.) (and (<= skoZ (+ (+ 2. (* skoX (- 1.))) (* skoY (- 1.)))) (<= (+ (+ 2. (* skoX (- 1.))) (* skoY (- 1.))) skoZ))))))))))
(set-info :status sat)
(check-sat)
