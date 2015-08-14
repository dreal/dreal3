(define (domain car)
(:requirements :typing :durative-actions :fluents :time
:negative-preconditions :timed-initial-literals)
(:constants T)
(:predicates (running) (stopped) (engineBlown))
(:functions (d) (v) (a) )

(:action startEngine
  :parameters()
  :precondition (and(stopped) )
  :effect (and (running) (not (stopped) ))
)

(:process moving
:parameters ()
:precondition (and (running))
:effect (and (increase (v) (* #t (a))) 
             (increase (d) (* #t (v))))
)

(:process windResistance
:parameters ()
:precondition (and (running) (>= (v) 50))
:effect (decrease (v) (* #t (* 0.1 (* (- (v) 50) (- (v) 50)))))
)


(:action accelerate
  :parameters()
  :precondition (and(running) )
  :effect (and (running) (increase a 1) )
)

(:action decelerate
  :parameters()
  :precondition (and(running))
  :effect (and (running)(decrease a 1))
)


(:event engineExplode
:parameters ()
:precondition (and (running) (>= (a) 1) (>= (v) 200))
:effect (and (not (running)) (engineBlown) (assign (a) 0))
)
)

(define (problem car_prob)
    (:domain car)
    (:init (not (engineBlown))
            (running)
            (= d 0)
            (= a 0)
            (= v 0))
     (:goal (and(= d 30) (= v 0) (not(engineBlown))))
     (:metric minimize(total-time))
)
