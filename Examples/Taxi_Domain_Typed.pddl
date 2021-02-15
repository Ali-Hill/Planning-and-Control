;; taxi domain
;;

(define (domain taxi)
  (:requirements :strips :typing)

   	(:types
   		taxi
   		location
   		person
    )

	(:predicates	 
	 (isIn ?obj1 - (either taxi person) ?l1 - location))
			 
	(:action drive_passenger
		:parameters
			(?t1 - taxi ?p1 - person ?l1 - location ?l2 - location)
		:precondition
			(and
				(isIn ?t1 ?l1)
				(isIn ?p1 ?l1))
		:effect
			(and
				(not (isIn ?t1 ?l1))
				(not (isIn ?p1 ?l1))
				(isIn ?t1 ?l2)
				(isIn ?p1 ?l2)))

	(:action drive
		:parameters
			(?t1 - taxi ?l1 - location ?l2 - location)
		:precondition
			(and
				(isIn ?t1 ?l1))
		:effect
			(and
				(not (isIn ?t1 ?l1))
				(isIn ?t1 ?l2))))	