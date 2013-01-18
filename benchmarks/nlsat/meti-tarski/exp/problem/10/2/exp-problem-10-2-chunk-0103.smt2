(set-logic QF_NRA)

(declare-fun skoSM1 () Real)
(declare-fun skoSP1 () Real)
(declare-fun skoX () Real)
(declare-fun skoS () Real)
(assert (and (not (<= (* skoSP1 (+ (/ (- 1.) 24794911296000.) (* skoSM1 (+ (/ (- 1.) 550998028800.) (* skoSM1 (+ (/ (- 1.) 20407334400.) (* skoSM1 (+ (/ (- 181.) 183666009600.) (* skoSM1 (+ (/ (- 1.) 62985600.) (* skoSM1 (+ (/ (- 361.) 1700611200.) (* skoSM1 (+ (/ (- 409.) 170061120.) (* skoSM1 (+ (/ (- 49.) 2099520.) (* skoSM1 (+ (/ (- 17.) 87480.) (* skoSM1 (+ (/ (- 121.) 87480.) (* skoSM1 (+ (/ (- 1.) 120.) (* skoSM1 (+ (/ (- 1.) 24.) (* skoSM1 (+ (/ (- 1.) 6.) (* skoSM1 (+ (/ (- 1.) 2.) (* skoSM1 (+ (- 1.) (* skoSM1 (- 2.)))))))))))))))))))))))))))))))) (* skoSM1 (* skoSM1 (* skoSM1 (* skoSM1 (* skoSM1 (* skoSM1 (* skoSM1 (* skoSM1 (* skoSM1 (* skoSM1 (* skoSM1 (* skoSM1 (* skoSM1 (* skoSM1 skoSM1)))))))))))))))) (and (not (<= skoX 1.)) (and (not (<= skoSP1 0.)) (and (not (<= skoSM1 0.)) (and (not (<= skoS 0.)) (not (<= 5. skoX))))))))
(set-info :status unsat)
(check-sat)
