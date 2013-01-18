(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (not (<= (* skoX (+ (+ (* skoC (/ 14336. 55.)) (* skoS (/ (- 395136.) 1375.))) (* skoX (+ (+ (* skoC (/ (- 25088.) 6875.)) (* skoS (/ 691488. 171875.))) (* skoX (+ (+ (* skoC (/ 87808. 2578125.)) (* skoS (/ (- 806736.) 21484375.))) (* skoX (+ (+ (* skoC (/ (- 67228.) 322265625.)) (* skoS (/ 2470629. 10742187500.))) (* skoX (+ (+ (* skoC (/ 33614. 40283203125.)) (* skoS (/ (- 2470629.) 2685546875000.))) (* skoX (+ (* skoC (/ (- 117649.) 60424804687500.)) (* skoS (/ 5764801. 2685546875000000.)))))))))))))) (+ (* skoC (/ 102400. 11.)) (* skoS (/ (- 112896.) 11.))))))
(set-info :status sat)
(check-sat)
