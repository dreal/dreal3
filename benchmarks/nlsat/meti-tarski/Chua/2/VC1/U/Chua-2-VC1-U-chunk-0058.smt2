(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoC () Real)
(declare-fun skoS () Real)
(assert (and (<= (* skoX (+ (/ (- 17920.) 11.) (* skoX (+ (/ 6272. 275.) (* skoX (+ (/ (- 21952.) 103125.) (* skoX (+ (/ 16807. 12890625.) (* skoX (+ (/ (- 16807.) 3222656250.) (* skoX (/ 117649. 9667968750000.)))))))))))) (/ (- 614656.) 11.)) (and (= (* skoS skoS) (+ 1. (* skoC (* skoC (- 1.))))) (and (<= skoX 75.) (<= 0. skoX)))))
(set-info :status unsat)
(check-sat)
