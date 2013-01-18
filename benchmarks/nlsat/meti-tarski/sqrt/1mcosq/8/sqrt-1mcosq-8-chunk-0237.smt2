(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun pi () Real)
(declare-fun skoX () Real)
(assert (and (not (<= (* skoY (* skoY (+ 1. (* skoY (* skoY (+ (/ (- 1.) 3.) (* skoY (* skoY (+ (/ 2. 45.) (* skoY (* skoY (+ (/ (- 127.) 40320.) (* skoY (* skoY (+ (/ 233. 1814400.) (* skoY (* skoY (+ (/ (- 743.) 239500800.) (* skoY (* skoY (+ (/ 2. 42567525.) (* skoY (* skoY (+ (/ (- 9949.) 20922789888000.) (* skoY (* skoY (+ (/ 10889. 3201186852864000.) (* skoY (* skoY (+ (/ (- 10949.) 608225502044160000.) (* skoY (* skoY (+ (/ 79. 1080769930555392000.) (* skoY (* skoY (+ (/ (- 3163.) 13488008733331292160000.) (* skoY (* skoY (+ (/ 41. 67440043666656460800000.) (* skoY (* skoY (/ (- 1.) 809280523999877529600000.)))))))))))))))))))))))))))))))))))))))))) 0.)) (and (not (<= skoY skoX)) (and (<= (/ 1. 10.) skoX) (and (not (<= (/ 31415927. 10000000.) pi)) (and (not (<= pi (/ 15707963. 5000000.))) (<= skoY (+ (/ (- 1.) 5.) (* pi (/ 1. 2.))))))))))
(set-info :status sat)
(check-sat)
