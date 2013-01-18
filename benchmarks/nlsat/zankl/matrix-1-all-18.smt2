(set-logic QF_NRA)
(set-info :source |
From termination analysis of term rewriting.

Submitted by Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun x3 () Real)
(declare-fun x0 () Real)
(declare-fun x4 () Real)
(declare-fun x1 () Real)
(declare-fun x5 () Real)
(declare-fun x2 () Real)
(assert (>= x3 0))
(assert (>= x0 0))
(assert (>= x4 0))
(assert (>= x1 0))
(assert (>= x5 0))
(assert (>= x2 0))
(assert (let ((?v_2 (+ x4 (* x5 x2)))) (let ((?v_1 (+ x0 (* x1 ?v_2))) (?v_0 (+ x0 (* x1 x2))) (?v_5 (* x5 x3))) (let ((?v_7 (* x1 ?v_5)) (?v_4 (* x1 x3)) (?v_12 (+ x2 (* x3 ?v_2)))) (let ((?v_8 (+ x4 (* x5 ?v_12)))) (let ((?v_3 (+ x0 (* x1 ?v_8))) (?v_14 (* x3 ?v_5))) (let ((?v_11 (* x5 ?v_14)) (?v_6 (+ x0 (* x1 x4)))) (let ((?v_15 (and (and (and (and (> ?v_0 ?v_1) (>= ?v_0 ?v_1)) (>= ?v_4 ?v_7)) (and (and (> ?v_0 ?v_3) (>= ?v_0 ?v_3)) (>= ?v_4 (* x1 ?v_11)))) (and (and (> ?v_1 ?v_6) (>= ?v_1 ?v_6)) (>= ?v_7 (* x1 x5))))) (?v_10 (+ x2 (* x3 ?v_8))) (?v_9 (+ x2 (* x3 x2))) (?v_13 (+ x2 (* x3 x4)))) (and (and (and ?v_15 (and (and (> ?v_9 ?v_10) (>= ?v_9 ?v_10)) (>= (* x3 x3) (* x3 ?v_11)))) (and (and (> ?v_12 ?v_13) (>= ?v_12 ?v_13)) (>= ?v_14 (* x3 x5)))) ?v_15)))))))))
(check-sat)
(exit)
