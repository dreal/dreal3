(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoY (* skoY (+ 1. (* skoY (* skoY (+ (/ (- 1.) 3.) (* skoY (* skoY (+ (/ 2. 45.) (* skoY (* skoY (+ (/ (- 1.) 315.) (* skoY (* skoY (+ (/ 2. 14175.) (* skoY (* skoY (+ (/ (- 2.) 467775.) (* skoY (* skoY (+ (/ 4. 42567525.) (* skoY (* skoY (+ (/ (- 5461.) 3487131648000.) (* skoY (* skoY (+ (/ 641. 31384184832000.) (* skoY (* skoY (+ (/ (- 199.) 941525544960000.) (* skoY (* skoY (+ (/ 17. 9886018222080000.) (* skoY (* skoY (+ (/ (- 223.) 20879270485032960000.) (* skoY (* skoY (+ (/ 1. 20879270485032960000.) (* skoY (* skoY (/ (- 1.) 7600054456551997440000.)))))))))))))))))))))))))))))))))))))))))) 0.) (and (not (<= (* skoY (* skoY (+ (/ 1. 2.) (* skoY (* skoY (+ (/ (- 1.) 24.) (* skoY (* skoY (+ (/ 1. 720.) (* skoY (* skoY (+ (/ (- 1.) 40320.) (* skoY (* skoY (+ (/ 1. 3628800.) (* skoY (* skoY (+ (/ (- 1.) 479001600.) (* skoY (* skoY (/ 1. 87178291200.))))))))))))))))))))) 1.)) (and (not (<= skoY skoX)) (and (<= (/ 1. 10.) skoX) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.)))))))))))
(set-info :status unsat)
(check-sat)
