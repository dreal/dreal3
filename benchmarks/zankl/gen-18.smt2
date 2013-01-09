(set-logic QF_NRA)
(set-info :source |
Harald Roman Zankl <Harald.Zankl@uibk.ac.at>

|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= (* a a) 2))
(assert (= (* b (* b b)) 2))
(assert (< a b))
(check-sat)
(exit)
