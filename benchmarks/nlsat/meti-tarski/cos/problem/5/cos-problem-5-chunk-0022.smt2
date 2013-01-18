(set-logic QF_NRA)

(declare-fun skoY () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (<= (* skoX (+ 2. skoX)) (- 1.)) (and (= (* skoY skoY) 3.) (and (not (<= pi (/ 15707963. 5000000.))) (and (not (<= (/ 31415927. 10000000.) pi)) (and (<= 0. skoY) (<= skoY skoX)))))))
(set-info :status unsat)
(check-sat)
