(set-logic QF_NRA)
(declare-fun xuscore2dollarsk!4 () Real)
(declare-fun vxuscore2dollarsk!5 () Real)
(declare-fun t21uscore0dollarsk!0 () Real)
(declare-fun a () Real)
(declare-fun vyuscore2dollarsk!6 () Real)
(declare-fun buscore2dollarsk!2 () Real)
(declare-fun yuscore2dollarsk!3 () Real)
(declare-fun stateuscore2dollarsk!1 () Real)
(declare-fun vx () Real)
(declare-fun vy () Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun b () Real)
(assert (= vyuscore2dollarsk!6
           (+ (- 2.0)
              (* a
                 (+ (- 2.0)
                    (* t21uscore0dollarsk!0 vxuscore2dollarsk!5)
                    xuscore2dollarsk!4)))))
(assert (= (+ (* vxuscore2dollarsk!5 vxuscore2dollarsk!5)
              (* vyuscore2dollarsk!6 vyuscore2dollarsk!6))
           8.0))
(assert (= vxuscore2dollarsk!5
           (+ 2.0
              (* (- 1.0)
                 a
                 (+ 2.0
                    (* t21uscore0dollarsk!0 vyuscore2dollarsk!6)
                    yuscore2dollarsk!3))
              (* 4.0 buscore2dollarsk!2 (+ 1.0 (* (- 1.0) a))))))
(assert (= stateuscore2dollarsk!1 1.0))
(assert (or (<= vxuscore2dollarsk!5 0.0) (not (>= t21uscore0dollarsk!0 0.0))))
(assert (>= t21uscore0dollarsk!0 0.0))
(assert (= stateuscore2dollarsk!1 2.0))
(assert (= vx 2.0))
(assert (= vy (- 2.0)))
(assert (= x 0.0))
(assert (= y 0.0))
(assert (= b 0.0))
(assert (not (= stateuscore2dollarsk!1 0.0)))
(assert (not (= vxuscore2dollarsk!5
                (+ 2.0
                   (* (- 1.0) a (+ 2.0 yuscore2dollarsk!3))
                   (* 4.0 buscore2dollarsk!2 (+ 1.0 (* (- 1.0) a)))))))
(assert (not (= (* a
                   (+ (* t21uscore0dollarsk!0 vxuscore2dollarsk!5)
                      xuscore2dollarsk!4
                      (* (- 1.0) t21uscore0dollarsk!0 vyuscore2dollarsk!6)
                      (* (- 1.0) yuscore2dollarsk!3)))
                (* (+ (- 4.0) (* (- 4.0) buscore2dollarsk!2))
                   (+ 1.0 (* (- 1.0) a))))))
(check-sat)
(exit)
