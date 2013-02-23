[
1.00
,
1.00
]
ID:x1
;
[
1.00
,
1.00
]
ID:x2
;
[
1.00
,
1.00
]
ID:x3
;
[
1.00
,
1.00
]
ID:x4
;
[
1.00
,
1.00
]
ID:x5
;
[
1.00
,
1.00
]
ID:x6
;
(
(
ID:not
(
(
<
(
+
(
*
1.00
(
*
5.00
(
-
0.05603050
)
)
)
(
*
1.00
(
*
0.04458130
(
*
2.00
3.14159265
)
)
)
)
0.00
)
)
)
)
(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert (<= 1.0 x1))
(assert (<= x1 1.0))
(assert (<= 1.0 x2))
(assert (<= x2 1.0))
(assert (<= 1.0 x3))
(assert (<= x3 1.0))
(assert (<= 1.0 x4))
(assert (<= x4 1.0))
(assert (<= 1.0 x5))
(assert (<= x5 1.0))
(assert (<= 1.0 x6))
(assert (<= x6 1.0))
(assert (not (< (+ (* 1.0 (* 5.0 (- 0.0560305))) (* 1.0 (* 0.0445813 (* 2.0 3.14159265)))) 0.0)))
(check-sat)
(exit)
