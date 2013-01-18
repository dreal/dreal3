(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= skoX 0.) (and (not (<= (* skoX (+ (/ (- 106368.) 13.) (* skoX (+ (/ 920748. 8125.) (* skoX (+ (/ (- 21253933.) 20312500.) (* skoX (+ (/ 41211376087. 6500000000000.) (* skoX (+ (/ (- 1630793025157.) 65000000000000000.) (* skoX (/ 451729667968489. 7800000000000000000000.)))))))))))) (/ (- 3810048.) 13.))) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX))))))
(set-info :status sat)
(check-sat)
