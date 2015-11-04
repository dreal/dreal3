(set-logic QF_NRA)
(set-info :precision 0.00001)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun s () Real)
(assert (< (+ (* x1 x1) (* x2 x2) (* x3 x3) (* x4 x4)) 0.01))

(assert (and (> s 0) (< s 1)))
(assert (= (* s s) (- (+ x1 0.89877559179912198425437882605416)
                      (* (+ x1 0.89877559179912198425437882605416)
                         (+ x1 0.89877559179912198425437882605416)))))

(assert (=  0.07
                        (+
                                (* 99.93480571  x1 x1)
                                (* 30.33988648  x1 x2)
                                (* (- 102.36911255) x1 x3)
                                (* 12.23908749  x1 x4)
                                (* 112.06951340 x1 (* x1 x1))
                                (* 53.98882124  x1 (* x1 x2))
                                (* 104.85634611 x1 (* x2 x2))
                                (* 90.39545543  x1 (* x1 x3))
                                (* 4.76548912   x1 (* x2 x3))
                                (* 128.60133992 x1 (* x3 x3))
                                (* 11.59236537  x1 (* x1 x4))
                                (* (- 11.88723162 ) x1 (* x2 x4))
                                (* 3.17269161   x1 (* x3 x4))
                                (* (- 41.43224247 ) x1 (* x4 x4))
                                (* 94.49599160  x2 x2)
                                (* (- 6.56262926  ) x2 x3)
                                (* 124.40733337 x2 x4)
                                (* 110.03260351 x2 (* x1 x1))
                                (* 160.26070647 x2 (* x1 x2))
                                (* (- 112.82732678) x2 (* x2 x2))
                                (* (- 17.64701753 ) x2 (* x1 x3))
                                (* 33.14166757  x2 (* x2 x3))
                                (* 49.21135585  x2 (* x3 x3))
                                (* (- 62.31715698 ) x2 (* x1 x4))
                                (* 155.37080703 x2 (* x2 x4))
                                (* 149.04126317 x2 (* x3 x4))
                                (* 118.17098043 x2 (* x4 x4))
                                (* 78.39144967  x3 x3)
                                (* 17.91122227  x3 x4)
                                (* 27.14962222  x3 (* x1 x1))
                                (* (- 61.25979053 ) x3 (* x1 x2))
                                (* (- 12.64530368 ) x3 (* x2 x2))
                                (* 22.25713016  x3 (* x1 x3))
                                (* 5.06103276   x3 (* x2 x3))
                                (* (- 29.56775941 ) x3 (* x3 x3))
                                (* 111.84648585 x3 (* x1 x4))
                                (* 19.03875013  x3 (* x2 x4))
                                (* (- 39.31429428 ) x3 (* x3 x4))
                                (* 78.07916558  x3 (* x4 x4))
                                (* 99.90378402  x4 x4)
                                (* 67.58958775  x4 (* x1 x1))
                                (* 39.96934692  x4 (* x1 x2))
                                (* (- 50.76131473 ) x4 (* x2 x2))
                                (* (- 40.65684216 ) x4 (* x1 x3))
                                (* 21.01300664  x4 (* x2 x3))
                                (* (- 9.20415544  ) x4 (* x3 x3))
                                (* 18.76615721  x4 (* x1 x4))
                                (* 123.17515793 x4 (* x2 x4))
                                (* 149.49396115 x4 (* x3 x4))
                                (* 9.58029820   x4 (* x4 x4))
                                (* 96.98046181  (* x1 x1) (* x1 x1))
                                (* 86.26931608  (* x1 x1) (* x1 x2))
                                (* 11.70584449  (* x1 x1) (* x2 x2))
                                (* 88.05269782  (* x1 x1) (* x1 x3))
                                (* 19.50487392  (* x1 x1) (* x2 x3))
                                (* 130.61630834 (* x1 x1) (* x3 x3))
                                (* 61.46239621  (* x1 x1) (* x1 x4))
                                (* 84.82402633  (* x1 x1) (* x2 x4))
                                (* 47.49059545  (* x1 x1) (* x3 x4))
                                (* 102.39369206 (* x1 x1) (* x4 x4))
                                (* 96.19286486  (* x1 x2) (* x1 x2))
                                (* (- 111.75991382) (* x1 x2) (* x2 x2))
                                (* (- 12.29053285 ) (* x1 x2) (* x1 x3))
                                (* 26.51188564  (* x1 x2) (* x2 x3))
                                (* 71.25939413  (* x1 x2) (* x3 x3))
                                (* (- 118.26497966) (* x1 x2) (* x1 x4))
                                (* 119.42455446 (* x1 x2) (* x2 x4))
                                (* 117.85584494 (* x1 x2) (* x3 x4))
                                (* 115.95639010 (* x1 x2) (* x4 x4))
                                (* 98.84561500  (* x2 x2) (* x2 x2))
                                (* 103.09289606 (* x2 x2) (* x1 x3))
                                (* (- 10.39592531 ) (* x2 x2) (* x2 x3))
                                (* 49.36208784  (* x2 x2) (* x3 x3))
                                (* 120.36280034 (* x2 x2) (* x1 x4))
                                (* (- 126.41483400) (* x2 x2) (* x2 x4))
                                (* (- 132.30287845) (* x2 x2) (* x3 x4))
                                (* (- 120.88926538) (* x2 x2) (* x4 x4))
                                (* 59.95019505  (* x1 x3) (* x1 x3))
                                (* 2.90167800   (* x1 x3) (* x2 x3))
                                (* 88.13882195  (* x1 x3) (* x3 x3))
                                (* 89.75457764  (* x1 x3) (* x1 x4))
                                (* (- 38.82077374 ) (* x1 x3) (* x2 x4))
                                (* (- 84.52342357 ) (* x1 x3) (* x3 x4))
                                (* 15.28362811  (* x1 x3) (* x4 x4))
                                (* 6.54968160   (* x2 x3) (* x2 x3))
                                (* 11.70034286  (* x2 x3) (* x3 x3))
                                (* (- 0.83321450  ) (* x2 x3) (* x1 x4))
                                (* 24.82532627  (* x2 x3) (* x2 x4))
                                (* 16.67487592  (* x2 x3) (* x3 x4))
                                (* 20.36353067  (* x2 x3) (* x4 x4))
                                (* 65.29014889  (* x3 x3) (* x3 x3))
                                (* 26.84494489  (* x3 x3) (* x1 x4))
                                (* 18.70852843  (* x3 x3) (* x2 x4))
                                (* (- 7.68874881  ) (* x3 x3) (* x3 x4))
                                (* 47.40079412  (* x3 x3) (* x4 x4))
                                (* 97.17953398  (* x1 x4) (* x1 x4))
                                (* (- 48.83097933 ) (* x1 x4) (* x2 x4))
                                (* (- 93.28360889 ) (* x1 x4) (* x3 x4))
                                (* (- 17.18972007 ) (* x1 x4) (* x4 x4))
                                (* 80.48480640  (* x2 x4) (* x2 x4))
                                (* 148.34930406 (* x2 x4) (* x3 x4))
                                (* 118.69942346 (* x2 x4) (* x4 x4))
                                (* 97.96466358  (* x3 x4) (* x3 x4))
                                (* 56.58992087  (* x3 x4) (* x4 x4))
                                (* 99.24526667  (* x4 x4) (* x4 x4))
                        )
                )
)


(assert (>
(+
        (*
                (+
                        (*
                                (+
                                        (* 99.93480571  x1)
                                        (* 15.16994324  x2)
                                        (* (- 51.18455628 ) x3)
                                        (* 6.11954375   x4)
                                        (* 56.03475670  (* x1 x1))
                                        (* 26.99441062  (* x1 x2))
                                        (* 52.42817306  (* x2 x2))
                                        (* 45.19772771  (* x1 x3))
                                        (* 2.38274456   (* x2 x3))
                                        (* 64.30066996  (* x3 x3))
                                        (* 5.79618268   (* x1 x4))
                                        (* (- 5.94361581  ) (* x2 x4))
                                        (* 1.58634581   (* x3 x4))
                                        (* (- 20.71612124 ) (* x4 x4))
                                )
                                1
                        )
                        (*
                                (+
                                        (* 56.03475670  x1)
                                        (* 55.01630175  x2)
                                        (* 13.57481111  x3)
                                        (* 33.79479387  x4)
                                        (* 96.98046181  (* x1 x1))
                                        (* 43.13465804  (* x1 x2))
                                        (* 5.85292224   (* x2 x2))
                                        (* 44.02634891  (* x1 x3))
                                        (* 9.75243696   (* x2 x3))
                                        (* 65.30815417  (* x3 x3))
                                        (* 30.73119810  (* x1 x4))
                                        (* 42.41201316  (* x2 x4))
                                        (* 23.74529772  (* x3 x4))
                                        (* 51.19684603  (* x4 x4))
                                )
                                (* 2 x1)
                        )
                        (*
                                (+
                                        (* 26.99441062  x1)
                                        (* 80.13035323  x2)
                                        (* (- 30.62989527 ) x3)
                                        (* 19.98467346  x4)
                                        (* 43.13465804  (* x1 x1))
                                        (* 96.19286486  (* x1 x2))
                                        (* (- 55.87995691 ) (* x2 x2))
                                        (* (- 6.14526642  ) (* x1 x3))
                                        (* 13.25594282  (* x2 x3))
                                        (* 35.62969706  (* x3 x3))
                                        (* (- 59.13248983 ) (* x1 x4))
                                        (* 59.71227723  (* x2 x4))
                                        (* 58.92792247  (* x3 x4))
                                        (* 57.97819505  (* x4 x4))
                                )
                                x2
                        )
                        (*
                                (+
                                        (* 45.19772771  x1)
                                        (* (- 8.82350876  ) x2)
                                        (* 11.12856508  x3)
                                        (* (- 20.32842108 ) x4)
                                        (* 44.02634891  (* x1 x1))
                                        (* (- 6.14526642  ) (* x1 x2))
                                        (* 51.54644803  (* x2 x2))
                                        (* 59.95019505  (* x1 x3))
                                        (* 1.45083900   (* x2 x3))
                                        (* 44.06941098  (* x3 x3))
                                        (* 44.87728882  (* x1 x4))
                                        (* (- 19.41038687 ) (* x2 x4))
                                        (* (- 42.26171179 ) (* x3 x4))
                                        (* 7.64181405   (* x4 x4))
                                )
                                x3
                        )
                        (*
                                (+
                                        (* 5.79618268   x1)
                                        (* (- 31.15857849 ) x2)
                                        (* 55.92324292  x3)
                                        (* 9.38307861   x4)
                                        (* 30.73119810  (* x1 x1))
                                        (* (- 59.13248983 ) (* x1 x2))
                                        (* 60.18140017  (* x2 x2))
                                        (* 44.87728882  (* x1 x3))
                                        (* (- 0.41660725  ) (* x2 x3))
                                        (* 13.42247245  (* x3 x3))
                                        (* 97.17953398  (* x1 x4))
                                        (* (- 24.41548966 ) (* x2 x4))
                                        (* (- 46.64180444 ) (* x3 x4))
                                        (* (- 8.59486003  ) (* x4 x4))
                                )
                                x4
                        )
                )
                (+ (* 19.07936 s) (- 5.754824342) (* (- 4.06771047571857) x1) (* 2.7855072 x1 x1))
        )
        (*
                (+
                        (*
                                (+
                                        (* 15.16994324  x1)
                                        (* 94.49599160  x2)
                                        (* (- 3.28131463  ) x3)
                                        (* 62.20366668  x4)
                                        (* 55.01630175  (* x1 x1))
                                        (* 80.13035323  (* x1 x2))
                                        (* (- 56.41366339 ) (* x2 x2))
                                        (* (- 8.82350876  ) (* x1 x3))
                                        (* 16.57083379  (* x2 x3))
                                        (* 24.60567792  (* x3 x3))
                                        (* (- 31.15857849 ) (* x1 x4))
                                        (* 77.68540351  (* x2 x4))
                                        (* 74.52063159  (* x3 x4))
                                        (* 59.08549021  (* x4 x4))
                                )
                                1
                        )
                        (*
                                (+
                                        (* 26.99441062  x1)
                                        (* 80.13035323  x2)
                                        (* (- 30.62989527 ) x3)
                                        (* 19.98467346  x4)
                                        (* 43.13465804  (* x1 x1))
                                        (* 96.19286486  (* x1 x2))
                                        (* (- 55.87995691 ) (* x2 x2))
                                        (* (- 6.14526642  ) (* x1 x3))
                                        (* 13.25594282  (* x2 x3))
                                        (* 35.62969706  (* x3 x3))
                                        (* (- 59.13248983 ) (* x1 x4))
                                        (* 59.71227723  (* x2 x4))
                                        (* 58.92792247  (* x3 x4))
                                        (* 57.97819505  (* x4 x4))
                                )
                                x1
                        )
                        (*
                                (+
                                        (* 52.42817306  x1)
                                        (* (- 56.41366339 ) x2)
                                        (* (- 6.32265184  ) x3)
                                        (* (- 25.38065737 ) x4)
                                        (* 5.85292224   (* x1 x1))
                                        (* (- 55.87995691 ) (* x1 x2))
                                        (* 98.84561500  (* x2 x2))
                                        (* 51.54644803  (* x1 x3))
                                        (* (- 5.19796265  ) (* x2 x3))
                                        (* 24.68104392  (* x3 x3))
                                        (* 60.18140017  (* x1 x4))
                                        (* (- 63.20741700 ) (* x2 x4))
                                        (* (- 66.15143923 ) (* x3 x4))
                                        (* (- 60.44463269 ) (* x4 x4))
                                )
                                (* 2 x2)
                        )
                        (*
                                (+
                                        (* 2.38274456   x1)
                                        (* 16.57083379  x2)
                                        (* 2.53051638   x3)
                                        (* 10.50650332  x4)
                                        (* 9.75243696   (* x1 x1))
                                        (* 13.25594282  (* x1 x2))
                                        (* (- 5.19796265  ) (* x2 x2))
                                        (* 1.45083900   (* x1 x3))
                                        (* 6.54968160   (* x2 x3))
                                        (* 5.85017143   (* x3 x3))
                                        (* (- 0.41660725  ) (* x1 x4))
                                        (* 12.41266314  (* x2 x4))
                                        (* 8.33743796   (* x3 x4))
                                        (* 10.18176533  (* x4 x4))
                                )
                                x3
                        )
                        (*
                                (+
                                        (* (- 5.94361581  ) x1)
                                        (* 77.68540351  x2)
                                        (* 9.51937507   x3)
                                        (* 61.58757897  x4)
                                        (* 42.41201316  (* x1 x1))
                                        (* 59.71227723  (* x1 x2))
                                        (* (- 63.20741700 ) (* x2 x2))
                                        (* (- 19.41038687 ) (* x1 x3))
                                        (* 12.41266314  (* x2 x3))
                                        (* 9.35426422   (* x3 x3))
                                        (* (- 24.41548966 ) (* x1 x4))
                                        (* 80.48480640  (* x2 x4))
                                        (* 74.17465203  (* x3 x4))
                                        (* 59.34971173  (* x4 x4))
                                )
                                x4
                        )
                )
                (* 4 (- (/ (+ 13.92475886 (* 9.84250502254783 x1) (* (- 0 6.74) x1 x1))
                                                   (+ 13.92475886 (* 5.56990354423028 x2) (* 6.68443252991542 x3)
                                                     (* 13.9247588605757 x4) (* 2.67377301196617 x2 x3)
                                                      (* (- 6.066) x3 x3) (* 6.68443252991542 x3 x4)
                                                      (* (- 2.4264) x2 x3 x3) (* (- 6.066) x3 x3 x4)
                                                   )
                                                )
                                                (+ x2 1)
                                             )
                                        )
        )
        (*
                (+
                        (*
                                (+
                                        (* (- 51.18455628 ) x1)
                                        (* (- 3.28131463  ) x2)
                                        (* 78.39144967  x3)
                                        (* 8.95561114   x4)
                                        (* 13.57481111  (* x1 x1))
                                        (* (- 30.62989527 ) (* x1 x2))
                                        (* (- 6.32265184  ) (* x2 x2))
                                        (* 11.12856508  (* x1 x3))
                                        (* 2.53051638   (* x2 x3))
                                        (* (- 14.78387970 ) (* x3 x3))
                                        (* 55.92324292  (* x1 x4))
                                        (* 9.51937507   (* x2 x4))
                                        (* (- 19.65714714 ) (* x3 x4))
                                        (* 39.03958279  (* x4 x4))
                                )
                                1
                        )
                        (*
                                (+
                                        (* 45.19772771  x1)
                                        (* (- 8.82350876  ) x2)
                                        (* 11.12856508  x3)
                                        (* (- 20.32842108 ) x4)
                                        (* 44.02634891  (* x1 x1))
                                        (* (- 6.14526642  ) (* x1 x2))
                                        (* 51.54644803  (* x2 x2))
                                        (* 59.95019505  (* x1 x3))
                                        (* 1.45083900   (* x2 x3))
                                        (* 44.06941098  (* x3 x3))
                                        (* 44.87728882  (* x1 x4))
                                        (* (- 19.41038687 ) (* x2 x4))
                                        (* (- 42.26171179 ) (* x3 x4))
                                        (* 7.64181405   (* x4 x4))
                                )
                                x1
                        )
                        (*
                                (+
                                        (* 2.38274456   x1)
                                        (* 16.57083379  x2)
                                        (* 2.53051638   x3)
                                        (* 10.50650332  x4)
                                        (* 9.75243696   (* x1 x1))
                                        (* 13.25594282  (* x1 x2))
                                        (* (- 5.19796265  ) (* x2 x2))
                                        (* 1.45083900   (* x1 x3))
                                        (* 6.54968160   (* x2 x3))
                                        (* 5.85017143   (* x3 x3))
                                        (* (- 0.41660725  ) (* x1 x4))
                                        (* 12.41266314  (* x2 x4))
                                        (* 8.33743796   (* x3 x4))
                                        (* 10.18176533  (* x4 x4))
                                )
                                x2
                        )
                        (*
                                (+
                                        (* 64.30066996  x1)
                                        (* 24.60567792  x2)
                                        (* (- 14.78387970 ) x3)
                                        (* (- 4.60207772  ) x4)
                                        (* 65.30815417  (* x1 x1))
                                        (* 35.62969706  (* x1 x2))
                                        (* 24.68104392  (* x2 x2))
                                        (* 44.06941098  (* x1 x3))
                                        (* 5.85017143   (* x2 x3))
                                        (* 65.29014889  (* x3 x3))
                                        (* 13.42247245  (* x1 x4))
                                        (* 9.35426422   (* x2 x4))
                                        (* (- 3.84437440  ) (* x3 x4))
                                        (* 23.70039706  (* x4 x4))
                                )
                                (* 2 x3)
                        )
                        (*
                                (+
                                        (* 1.58634581   x1)
                                        (* 74.52063159  x2)
                                        (* (- 19.65714714 ) x3)
                                        (* 74.74698057  x4)
                                        (* 23.74529772  (* x1 x1))
                                        (* 58.92792247  (* x1 x2))
                                        (* (- 66.15143923 ) (* x2 x2))
                                        (* (- 42.26171179 ) (* x1 x3))
                                        (* 8.33743796   (* x2 x3))
                                        (* (- 3.84437440  ) (* x3 x3))
                                        (* (- 46.64180444 ) (* x1 x4))
                                        (* 74.17465203  (* x2 x4))
                                        (* 97.96466358  (* x3 x4))
                                        (* 28.29496044  (* x4 x4))
                                )
                                x4
                        )
                )
                (+ (* 19.07936 s) (- 5.754824342) (* (- 2.76254227596344) x3) (* 2.50695648 x3 x3))
        )
        (*
                (+
                        (*
                                (+
                                        (* 6.11954375   x1)
                                        (* 62.20366668  x2)
                                        (* 8.95561114   x3)
                                        (* 99.90378402  x4)
                                        (* 33.79479387  (* x1 x1))
                                        (* 19.98467346  (* x1 x2))
                                        (* (- 25.38065737 ) (* x2 x2))
                                        (* (- 20.32842108 ) (* x1 x3))
                                        (* 10.50650332  (* x2 x3))
                                        (* (- 4.60207772  ) (* x3 x3))
                                        (* 9.38307861   (* x1 x4))
                                        (* 61.58757897  (* x2 x4))
                                        (* 74.74698057  (* x3 x4))
                                        (* 4.79014910   (* x4 x4))
                                )
                                1
                        )
                        (*
                                (+
                                        (* 5.79618268   x1)
                                        (* (- 31.15857849 ) x2)
                                        (* 55.92324292  x3)
                                        (* 9.38307861   x4)
                                        (* 30.73119810  (* x1 x1))
                                        (* (- 59.13248983 ) (* x1 x2))
                                        (* 60.18140017  (* x2 x2))
                                        (* 44.87728882  (* x1 x3))
                                        (* (- 0.41660725  ) (* x2 x3))
                                        (* 13.42247245  (* x3 x3))
                                        (* 97.17953398  (* x1 x4))
                                        (* (- 24.41548966 ) (* x2 x4))
                                        (* (- 46.64180444 ) (* x3 x4))
                                        (* (- 8.59486003  ) (* x4 x4))
                                )
                                x1
                        )
                        (*
                                (+
                                        (* (- 5.94361581  ) x1)
                                        (* 77.68540351  x2)
                                        (* 9.51937507   x3)
                                        (* 61.58757897  x4)
                                        (* 42.41201316  (* x1 x1))
                                        (* 59.71227723  (* x1 x2))
                                        (* (- 63.20741700 ) (* x2 x2))
                                        (* (- 19.41038687 ) (* x1 x3))
                                        (* 12.41266314  (* x2 x3))
                                        (* 9.35426422   (* x3 x3))
                                        (* (- 24.41548966 ) (* x1 x4))
                                        (* 80.48480640  (* x2 x4))
                                        (* 74.17465203  (* x3 x4))
                                        (* 59.34971173  (* x4 x4))
                                )
                                x2
                        )
                        (*
                                (+
                                        (* 1.58634581   x1)
                                        (* 74.52063159  x2)
                                        (* (- 19.65714714 ) x3)
                                        (* 74.74698057  x4)
                                        (* 23.74529772  (* x1 x1))
                                        (* 58.92792247  (* x1 x2))
                                        (* (- 66.15143923 ) (* x2 x2))
                                        (* (- 42.26171179 ) (* x1 x3))
                                        (* 8.33743796   (* x2 x3))
                                        (* (- 3.84437440  ) (* x3 x3))
                                        (* (- 46.64180444 ) (* x1 x4))
                                        (* 74.17465203  (* x2 x4))
                                        (* 97.96466358  (* x3 x4))
                                        (* 28.29496044  (* x4 x4))
                                )
                                x3
                        )
                        (*
                                (+
                                        (* (- 20.71612124 ) x1)
                                        (* 59.08549021  x2)
                                        (* 39.03958279  x3)
                                        (* 4.79014910   x4)
                                        (* 51.19684603  (* x1 x1))
                                        (* 57.97819505  (* x1 x2))
                                        (* (- 60.44463269 ) (* x2 x2))
                                        (* 7.64181405   (* x1 x3))
                                        (* 10.18176533  (* x2 x3))
                                        (* 23.70039706  (* x3 x3))
                                        (* (- 8.59486003  ) (* x1 x4))
                                        (* 59.34971173  (* x2 x4))
                                        (* 28.29496044  (* x3 x4))
                                        (* 99.24526667  (* x4 x4))
                                )
                                (* 2 x4)
                        )
                )
                (* 0.4 x2)
        )
) -0.00001)
)


(check-sat)
(exit)
