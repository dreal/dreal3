(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ (/ (- 1656.) 125.) (* skoX (+ (/ (- 4761.) 125000.) (* skoX (+ (/ (- 36501.) 500000000.) (* skoX (+ (/ (- 5876661.) 64000000000000.) (* skoX (+ (/ (- 19309029.) 256000000000000000.) (* skoX (/ (- 148035889.) 4096000000000000000000.)))))))))))) 2304.)) (or (not (<= (* skoC (/ 86400000. 2025130727.)) skoS)) (not (<= skoS (* skoC (/ 86400000. 2025130727.)))))))
(set-info :status unsat)
(check-sat)
