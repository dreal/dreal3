(set-logic QF_NRA)

(declare-fun skoM () Real)
(declare-fun skoS () Real)
(declare-fun skoSINS () Real)
(declare-fun skoCOSS () Real)
(assert (and (<= (* skoSINS (+ (+ (* skoM (* skoM (* skoM (+ (* skoCOSS (- 2.)) (* skoM (- 5.)))))) (* skoS (+ (* skoM (* skoM (* skoM (* skoM (- 3.))))) (* skoS (+ (* skoM (* skoM (* skoM (* skoM 3.)))) (* skoS (* skoM (* skoM (* skoM skoM))))))))) (* skoSINS (+ (* skoM (* skoM skoM)) (* skoS (* skoM (* skoM skoM))))))) (+ (* skoM (* skoM (* skoM (+ (* skoCOSS (* skoCOSS (- 2.))) (* skoM (+ (* skoCOSS (- 6.)) (* skoM (- 2.)))))))) (* skoS (+ (* skoM (* skoM (* skoM (+ (* skoCOSS (* skoCOSS (- 2.))) (* skoM (+ (* skoCOSS (- 12.)) (* skoM (- 6.)))))))) (* skoS (+ (* skoM (* skoM (* skoM (* skoM (+ (* skoCOSS (- 6.)) (* skoM (- 6.))))))) (* skoS (* skoM (* skoM (* skoM (* skoM (* skoM (- 2.))))))))))))) (and (not (<= (* skoM skoM) 0.)) (and (= (* skoSINS skoSINS) (+ 1. (* skoCOSS (* skoCOSS (- 1.))))) (and (<= 2. skoS) (<= 2. skoM))))))
(set-info :status unsat)
(check-sat)
