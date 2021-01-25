;
; Taxi Problem
;
(define (problem taxi-problem1)
  (:domain taxi)

  (:objects
      taxi1
      taxi2
      taxi3
      person1
      person2
      person3
      location1
      location2
      location3
  )

  (:init
	(isIn taxi1 location1)
	(isIn taxi2 location2)
	(isIn taxi3 location3)
	(isIn person1 location1)
	(isIn person2 location2)
	(isIn person3 location3))
	
  (:goal
      (and
	(isIn taxi1 location2)
	(isIn person1 location3)
	(isIn person3 location1)
      )
  )
)
