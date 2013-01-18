(set-logic QF_NRA)

(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (not (<= (* skoZ (+ (+ (+ 180. (* skoX (+ (- 153.) (* skoX (+ (/ (- 45.) 2.) (* skoX (/ (- 27.) 4.))))))) (* skoY (+ (+ (- 153.) (* skoX (+ (- 45.) (* skoX (/ (- 81.) 4.))))) (* skoY (+ (+ (/ (- 45.) 2.) (* skoX (/ (- 81.) 4.))) (* skoY (/ (- 27.) 4.))))))) (* skoZ (+ (+ (+ (- 174.) (* skoX (+ (- 18.) (* skoX (+ (/ (- 39.) 4.) (* skoX (/ 9. 8.))))))) (* skoY (+ (+ (- 18.) (* skoX (+ (/ (- 39.) 2.) (* skoX (/ 27. 8.))))) (* skoY (+ (+ (/ (- 39.) 4.) (* skoX (/ 27. 8.))) (* skoY (/ 9. 8.))))))) (* skoZ (+ (+ (+ 18. (* skoX (+ (/ 3. 4.) (* skoX (/ 27. 8.))))) (* skoY (+ (+ (/ 3. 4.) (* skoX (/ 27. 4.))) (* skoY (/ 27. 8.))))) (* skoZ (+ (+ (+ (/ 15. 4.) (* skoX (/ 27. 8.))) (* skoY (/ 27. 8.))) (* skoZ (/ 9. 8.)))))))))) (+ (+ (- 1260.) (* skoX (+ (- 810.) (* skoX (+ (- 126.) (* skoX (/ (- 27.) 2.))))))) (* skoY (+ (+ (- 810.) (* skoX (+ (- 252.) (* skoX (/ (- 81.) 2.))))) (* skoY (+ (+ (- 126.) (* skoX (/ (- 81.) 2.))) (* skoY (/ (- 27.) 2.))))))))))
(set-info :status sat)
(check-sat)
