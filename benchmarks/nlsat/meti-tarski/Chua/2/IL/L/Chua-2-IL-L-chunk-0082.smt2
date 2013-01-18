(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(assert (and (not (<= (* skoX (+ (+ (* skoC (/ 14958. 40625.)) (* skoS (/ (- 560961211379.) 65000000000.))) (* skoX (+ (* skoC (/ (- 690561.) 406250000.)) (* skoS (/ 155386255551983. 3900000000000000.)))))) (+ (* skoC (/ 1728. 65.)) (* skoS (/ (- 2025130727.) 3250000.))))) (or (not (<= (* skoC (/ 86400000. 2025130727.)) skoS)) (not (<= skoS (* skoC (/ 86400000. 2025130727.)))))))
(set-info :status sat)
(check-sat)
