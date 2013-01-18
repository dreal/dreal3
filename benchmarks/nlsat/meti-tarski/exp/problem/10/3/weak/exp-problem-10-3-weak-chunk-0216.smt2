(set-logic QF_NRA)

(declare-fun skoC () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoX () Real)
(assert (and (not (<= 0. skoCM1)) (and (not (<= (* skoCM1 (+ 1. (* skoC (+ (- 48.) (* skoC (+ 1248. (* skoC (+ (- 22272.) (* skoC (+ 297216. (* skoC (+ (- 3096576.) (* skoC (+ 25657344. (* skoC (+ (- 169869312.) (* skoC (+ 891813888. (* skoC (+ (- 3623878656.) (* skoC (+ 10871635968. (* skoC (- 21743271936.)))))))))))))))))))))))) (+ (- 1.) (* skoC (+ 48. (* skoC (+ (- 1248.) (* skoC (+ 22272. (* skoC (+ (- 297216.) (* skoC (+ 3096576. (* skoC (+ (- 25657344.) (* skoC (+ 169869312. (* skoC (+ (- 891813888.) (* skoC (+ 3623878656. (* skoC (+ (- 10871635968.) (* skoC (+ 21743271936. (* skoC (- 21743271936.))))))))))))))))))))))))))) (and (not (<= skoX 1.)) (and (not (<= skoCM1 0.)) (not (<= skoC 0.)))))))
(set-info :status unsat)
(check-sat)
