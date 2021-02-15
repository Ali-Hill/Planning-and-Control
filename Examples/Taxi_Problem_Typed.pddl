;
; Taxi Problem
;
(define (problem taxi-problem1)
  (:domain taxi)

  (:objects
      taxi1 taxi2 taxi3 - taxi
      person1 person2 person3 - person
      location1 location2 location3 - location
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
