[
1.00
,
1.175479655730
]
ID:x1
;
[
1.00
,
1.175479655730
]
ID:x2
;
[
1.00
,
1.175479655730
]
ID:x3
;
[
5.66440
,
9.06010
]
ID:x4
;
[
4.0
,
6.35040
]
ID:x5
;
[
6.250
,
15.530
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
*
(
*
(
-
4.00
)
(
+
(
*
(
^
ID:x4
2.0
)
ID:x1
)
(
-
(
*
8.00
(
*
(
-
ID:x5
ID:x6
)
(
-
ID:x2
ID:x3
)
)
)
(
*
ID:x4
(
+
(
*
16.00
ID:x1
)
(
+
(
*
(
-
ID:x5
8.00
)
ID:x2
)
(
*
(
-
ID:x6
8.00
)
ID:x3
)
)
)
)
)
)
)
(
-
1.00
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
(assert (<= x1 1.17547965573))
(assert (<= 1.0 x2))
(assert (<= x2 1.17547965573))
(assert (<= 1.0 x3))
(assert (<= x3 1.17547965573))
(assert (<= 5.6644 x4))
(assert (<= x4 9.0601))
(assert (<= 4.0 x5))
(assert (<= x5 6.3504))
(assert (<= 6.25 x6))
(assert (<= x6 15.53))
(assert (not (< (* (* (- 4.0) (+ (* (^ x4 2.0) x1) (- (* 8.0 (* (- x5 x6) (- x2 x3))) (* x4 (+ (* 16.0 x1) (+ (* (- x5 8.0) x2) (* (- x6 8.0) x3))))))) (- 1.0)) 0.0)))
(check-sat)
(exit)
