[
4.0
,
6.35040
]
ID:x1
;
[
4.0
,
4.0
]
ID:x2
;
[
4.0
,
6.35040
]
ID:x3
;
[
9.06010
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
4.0
,
4.0
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
-
(
*
(
-
ID:x2
)
ID:x3
)
(
*
ID:x1
ID:x4
)
)
(
+
(
*
ID:x2
ID:x5
)
(
+
(
-
(
*
ID:x3
ID:x6
)
(
*
ID:x5
ID:x6
)
)
(
*
ID:x1
(
+
(
-
ID:x1
)
(
+
ID:x2
(
+
(
-
ID:x3
ID:x4
)
(
+
ID:x5
ID:x6
)
)
)
)
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
(assert (<= 4.0 x1))
(assert (<= x1 6.3504))
(assert (<= 4.0 x2))
(assert (<= x2 4.0))
(assert (<= 4.0 x3))
(assert (<= x3 6.3504))
(assert (<= 9.0601 x4))
(assert (<= x4 9.0601))
(assert (<= 4.0 x5))
(assert (<= x5 6.3504))
(assert (<= 4.0 x6))
(assert (<= x6 4.0))
(assert (not (< (+ (- (* (- x2) x3) (* x1 x4)) (+ (* x2 x5) (+ (- (* x3 x6) (* x5 x6)) (* x1 (+ (- x1) (+ x2 (+ (- x3 x4) (+ x5 x6)))))))) 0.0)))
(check-sat)
(exit)
