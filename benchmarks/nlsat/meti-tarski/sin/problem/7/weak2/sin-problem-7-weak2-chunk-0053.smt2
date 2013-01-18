(set-logic QF_NRA)

(declare-fun skoA () Real)
(declare-fun skoX () Real)
(declare-fun pi () Real)
(assert (and (not (<= 0. skoA)) (and (not (<= (* skoA (/ 1. 2000.)) skoX)) (and (or (not (<= (* skoA (/ 1. 2000.)) skoX)) (not (<= skoX (* skoA (/ 1. 2000.))))) (and (not (<= skoA skoX)) (and (not (<= skoX 0.)) (and (not (<= (* pi (/ 1. 2.)) skoA)) (and (not (<= (/ 31415927. 10000000.) pi)) (not (<= pi (/ 15707963. 5000000.)))))))))))
(set-info :status unsat)
(check-sat)
