;; taxi domain
;;

(define (domain taxi)
  (:requirements :strips) 
  (:predicates	 (taxi ?taxi1)
  		 (person ?person1)
		 (location ?location1)
		 (isIn ?obj1 ?location1))
		 
(:action drive_passenger
	:parameters
		(?t1 ?p1 ?l1 ?l2)
	:precondition
		(and
			(isIn ?t1 ?location1)
			(isIn ?person1 ?location1)
	:effect
		(and
			(not (isIn ?taxi1 ?location1))
			(not (isIn ?person1 ?location1))
			(isIn ?taxi1 ?location2)
			(isIn ?person1 ?location2)))

(:action drive
	:parameters
		(?taxi1 ?location1 ?location2)
	:precondition
		(and
			(isIn ?taxi1 ?location1))
		(and
			(not (isIn ?taxi1 ?location1))
			(isIn ?taxi1 ?location2))))			

