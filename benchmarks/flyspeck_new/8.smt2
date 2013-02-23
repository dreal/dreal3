[
4.00
,
4.04010
]
ID:x1
;
[
4.00
,
4.04010
]
ID:x2
;
[
7.840
,
8.00
]
ID:x3
;
[
4.00
,
4.04010
]
ID:x4
;
[
4.00
,
4.04010
]
ID:x5
;
[
7.840
,
8.00
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
(assert (<= 4.0 x1))
(assert (<= x1 4.0401))
(assert (<= 4.0 x2))
(assert (<= x2 4.0401))
(assert (<= 7.84 x3))
(assert (<= x3 8.0))
(assert (<= 4.0 x4))
(assert (<= x4 4.0401))
(assert (<= 4.0 x5))
(assert (<= x5 4.0401))
(assert (<= 7.84 x6))
(assert (<= x6 8.0))
(assert (not (< (* (+ (- (* (- x2) x3) (* x1 x4)) (+ (* x2 x5) (+ (- (* x3 x6) (* x5 x6)) (* x1 (+ (- x1) (+ x2 (+ (- x3 x4) (+ x5 x6)))))))) (- 1.0)) 0.0)))
(check-sat)
(exit)
