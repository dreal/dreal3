(set-logic QF_NRA)
(declare-fun stuscore2dollarsk_0 () Real)
(declare-fun vuscore2dollarsk_4 () Real)
(declare-fun tuscore2dollarsk_1 () Real)
(declare-fun suscore2dollarsk_2 () Real)
(declare-fun zuscore2dollarsk_3 () Real)
(assert (= stuscore2dollarsk_0 0.0))
(assert (= vuscore2dollarsk_4 200.0))
(assert (= zuscore2dollarsk_3
           (+ (* 4000.0 suscore2dollarsk_2)
              (* tuscore2dollarsk_1
                 tuscore2dollarsk_1
                 (+ 5.0 (* (- 5.0) stuscore2dollarsk_0)))
              (* stuscore2dollarsk_0
                 (+ 2000.0
                    (* 200.0 tuscore2dollarsk_1)
                    (* (- 5.0) tuscore2dollarsk_1 tuscore2dollarsk_1))))))
(assert (>= tuscore2dollarsk_1 0.0))
(assert (>= suscore2dollarsk_2 0.0))
(assert (>= vuscore2dollarsk_4 0.0))
(assert (>= zuscore2dollarsk_3 0.0))
(assert (= vuscore2dollarsk_4
           (+ (* tuscore2dollarsk_1 (+ 10.0 (* (- 10.0) stuscore2dollarsk_0)))
              (* stuscore2dollarsk_0 (+ 200.0 (* (- 10.0) tuscore2dollarsk_1))))))
(assert (not (= zuscore2dollarsk_3 (+ 2000.0 (* 4000.0 suscore2dollarsk_2)))))
(check-sat)
(exit)
