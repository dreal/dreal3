(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (<= (* skoX (* skoX (+ (- 1.) (* skoX (* skoX (+ (/ 1. 3.) (* skoX (* skoX (+ (/ (- 2.) 45.) (* skoX (* skoX (+ (/ 1. 315.) (* skoX (* skoX (+ (/ (- 2.) 14175.) (* skoX (* skoX (+ (/ 2. 467775.) (* skoX (* skoX (+ (/ (- 4.) 42567525.) (* skoX (* skoX (+ (/ 5461. 3487131648000.) (* skoX (* skoX (+ (/ (- 641.) 31384184832000.) (* skoX (* skoX (+ (/ 199. 941525544960000.) (* skoX (* skoX (+ (/ (- 17.) 9886018222080000.) (* skoX (* skoX (+ (/ 223. 20879270485032960000.) (* skoX (* skoX (+ (/ (- 1.) 20879270485032960000.) (* skoX (* skoX (/ 1. 7600054456551997440000.)))))))))))))))))))))))))))))))))))))))))) 0.) (and (not (<= skoY skoX)) (and (<= (/ 1. 10.) skoX) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.))))))))))
(set-info :status sat)
(check-sat)
