(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ (- 1656.) 125.) (* skoX (+ (/ (- 4761.) 125000.) (* skoX (+ (/ (- 36501.) 500000000.) (* skoX (+ (/ (- 5876661.) 64000000000000.) (* skoX (+ (/ (- 19309029.) 256000000000000000.) (* skoX (/ (- 148035889.) 4096000000000000000000.)))))))))))) 2304.) (and (not (<= skoX 0.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX))))))
(set-info :status sat)
(check-sat)
