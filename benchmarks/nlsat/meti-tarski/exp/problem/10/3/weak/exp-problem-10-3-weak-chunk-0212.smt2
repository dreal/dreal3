(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(assert (and (<= (* skoC (+ 48. (* skoC (+ (- 1248.) (* skoC (+ 22272. (* skoC (+ (- 297216.) (* skoC (+ 3096576. (* skoC (+ (- 25657344.) (* skoC (+ 169869312. (* skoC (+ (- 891813888.) (* skoC (+ 3623878656. (* skoC (+ (- 10871635968.) (* skoC (+ 21743271936. (* skoC (- 21743271936.)))))))))))))))))))))))) 1.) (and (not (<= (* skoCM1 (+ 12. (* skoCM1 (+ (- 60.) (* skoCM1 120.))))) 1.)) (and (= (+ 1. (* skoCM1 (* skoCM1 skoCM1))) skoX) (and (= (* skoC (* skoC skoC)) skoX) (and (not (<= skoX 1.)) (and (not (<= skoCM1 0.)) (not (<= skoC 0.)))))))))
(set-info :status sat)
(check-sat)
