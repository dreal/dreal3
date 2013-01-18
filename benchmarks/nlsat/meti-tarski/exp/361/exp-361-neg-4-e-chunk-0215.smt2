(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun e () Real)
(declare-fun a () Real)
(assert (and (not (= a 4.)) (and (not (<= (* skoX (+ (- 1536.) (* skoX (+ (- 256.) (* skoX (* skoX (+ (* e (* e (* e (* e (/ 29997. 2500.))))) (* skoX (+ (* e (* e (* e (* e (/ (- 30003.) 5000.))))) (* skoX (* e (* e (* e (* e (/ 9999. 10000.))))))))))))))) 3072.)) (and (not (<= e 0.)) (not (<= skoX 0.))))))
(set-info :status sat)
(check-sat)
