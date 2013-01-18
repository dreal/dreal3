(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoX () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoCP1 () Real)
(assert (and (not (= (* skoC (* skoC skoC)) skoX)) (and (<= 0. skoCP1) (and (<= 0. skoCM1) (and (<= 0. skoC) (not (<= skoX (/ 7. 5.))))))))
(set-info :status sat)
(check-sat)
