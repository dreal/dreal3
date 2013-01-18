(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun e () Real)
(declare-fun a () Real)
(assert (and (not (= a 6.)) (and (not (<= (* skoX (+ (- 1.) (* skoX (+ (/ (- 1.) 2.) (* skoX (+ (/ (- 1.) 6.) (* skoX (+ (/ (- 1.) 24.) (* skoX (+ (/ (- 1.) 120.) (* skoX (+ (+ (/ (- 121.) 87480.) (* e (* e (* e (* e (* e (* e (/ 1. 46656.)))))))) (* skoX (+ (/ (- 17.) 87480.) (* skoX (+ (/ (- 49.) 2099520.) (* skoX (+ (/ (- 409.) 170061120.) (* skoX (+ (/ (- 361.) 1700611200.) (* skoX (+ (/ (- 1.) 62985600.) (* skoX (+ (/ (- 181.) 183666009600.) (* skoX (+ (/ (- 1.) 20407334400.) (* skoX (+ (/ (- 1.) 550998028800.) (* skoX (/ (- 1.) 24794911296000.)))))))))))))))))))))))))))))) (/ 159. 50.))) (and (not (<= (* skoX (+ (- 1.) (* skoX (* skoX (* skoX (* skoX (* skoX (* e (* e (* e (* e (* e (* e (/ 1. 46656.)))))))))))))) (/ 159. 50.))) (and (not (<= (* skoX (* skoX (* skoX (* skoX (* skoX (* skoX (* e (* e (* e (* e (* e (* e (/ 1. 46656.))))))))))))) (/ 109. 50.))) (and (not (<= e 0.)) (not (<= skoX 0.))))))))
(set-info :status sat)
(check-sat)
