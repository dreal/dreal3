(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ (/ (- 8832.) 13.) (* skoX (+ (/ (- 3174.) 1625.) (* skoX (+ (/ (- 12167.) 3250000.) (* skoX (+ (/ (- 1958887.) 416000000000.) (* skoX (+ (/ (- 6436343.) 1664000000000000.) (* skoX (/ (- 148035889.) 79872000000000000000.)))))))))))) (+ (+ (/ 1536000. 13.) (* skoC (/ 331776. 65.))) (* skoS (/ (- 24301568724.) 203125.))))) (or (not (<= (* skoC (/ 86400000. 2025130727.)) skoS)) (not (<= skoS (* skoC (/ 86400000. 2025130727.)))))))
(set-info :status sat)
(check-sat)
