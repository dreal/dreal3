(set-logic QF_NRA)

(declare-fun skoX () Real)
(declare-fun skoSX () Real)
(declare-fun skoSMX () Real)
(assert (and (<= skoSMX skoSX) (and (<= (* skoX (+ (+ (+ (- 24.) (* skoSMX (- 6.))) (* skoSX (- 6.))) (* skoX (+ (+ (* skoSMX 24.) (* skoSX (- 24.))) (* skoX (+ (+ 12. (* skoSMX 3.)) (* skoSX 3.))))))) (+ (* skoSMX 36.) (* skoSX (- 36.)))) (and (<= (* skoX (+ (+ (+ (- 12.) (* skoSMX (- 3.))) (* skoSX (- 3.))) (* skoX (+ (* skoSMX 6.) (* skoSX (- 6.)))))) (+ (* skoSMX 18.) (* skoSX (- 18.)))) (and (not (<= skoX 0.)) (and (<= 0. skoSMX) (and (<= 0. skoSX) (and (<= skoX 1.) (and (= (+ (- 1.) (* skoSX skoSX)) skoX) (= skoX (+ 1. (* skoSMX (* skoSMX (- 1.))))))))))))))
(set-info :status sat)
(check-sat)
