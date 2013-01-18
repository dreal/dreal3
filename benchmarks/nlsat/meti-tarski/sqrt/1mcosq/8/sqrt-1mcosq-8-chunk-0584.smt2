(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun pi () Real)
(declare-fun skoY () Real)
(assert (and (not (<= (* skoX (* skoX (/ (- 1.) 2.))) (- 1.))) (and (not (<= skoY skoX)) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))
(set-info :status sat)
(check-sat)
