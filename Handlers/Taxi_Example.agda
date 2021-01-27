open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.List hiding (any)
open import Relation.Nullary
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Empty
open import Data.Product
open import Data.Sum

open import Handlers.Taxi_Domain_Types
open import Agda.Builtin.Nat
open import Data.List

module Handlers.Taxi_Example  where

open import Grammar_Types {Action} {R} {Type} {C} renaming (NPred to State) hiding (¬_)

----------------------------------------------------------------------------------------

open import Data.Product

-- Action Context which defines the preconditions and effects of Actions.
Γ₁ : Γ
Γ₁ (drivePassenger t1 p1 l1 l2) = (+ , isIn t1 l1) ∷
                                  (+ , isIn p1 l1) ∷ []
                                                        ,
                                                        (- , isIn t1 l1) ∷
                                                        (- , isIn p1 l1) ∷
                                                        (+ , isIn t1 l2) ∷
                                                        (+ , isIn p1 l2) ∷ []
Γ₁ (drive t1 l1 l2) = (+ , isIn t1 l1) ∷ []
                                         ,
                                           (- , isIn t1 l1) ∷
                                           (+ , isIn t1 l2) ∷ []

----------------------------------------------------------------------------------------


open Data.Product renaming (_,_ to _↝_)

-- Initial State
P : State
P = (+ ↝ (isIn taxi1 location1)) ∷ (+ ↝ (isIn taxi2 location2)) ∷ (+ ↝ (isIn taxi3 location3)) ∷ (+ ↝ (isIn person1 location1)) ∷ (+ ↝ (isIn person2 location2)) ∷ (+ ↝ (isIn person3 location3)) ∷ []

-- Goal State
Q : State
Q = (+ ↝ (isIn taxi1 location2)) ∷ (+ ↝ (isIn person1 location3)) ∷ (+ ↝ (isIn person3 location1)) ∷ []

open import Relation.Nullary.Decidable
open import Data.Unit

-- Example Plan to get from P to Q produced by an online planner.
plan₁ : Plan
plan₁ = doAct (drive taxi1 location1 location2) (doAct (drivePassenger taxi3 person3 location3 location1) (doAct (drivePassenger taxi3 person1 location1 location3) halt))

open import PCPlans_Typed {Action} {R} {Type} {C} {isDecidable} {isDEC} {isDECA}
open import Data.Maybe

-- The below function asks us to construct in our type system that applying plan₁ to P entails Q given the context Γ₁.
-- This has been proven true in our type system using our automated solver function.
proofOfPlan : Γ₁ ⊢ plan₁ ∶ P ↝ Q
proofOfPlan = from-just (solver Γ₁ plan₁ P Q)

----------------------------------------------------------------------------------------
-- Examples with handlers 

-- Example numberOfTrips function giving the number of trips each taxi has taken.
numberOfTrips : C taxi -> Nat
numberOfTrips taxi1 = 0
numberOfTrips taxi2 = 0
numberOfTrips taxi3 = 0

-- Example maxTrips function giving the maximum number of trips for each taxi.
maxTrips : C taxi -> Nat
maxTrips x = 2

open import Handlers.Taxi_Typed {numberOfTrips} {maxTrips}

-- Convert a State to a World
stateToWorld : State  -> World
stateToWorld [] = []
stateToWorld ((+ , a) ∷ S) = a ∷ stateToWorld S
stateToWorld ((- , a) ∷ S) = stateToWorld S

----------------------------------------------------------------------------------------
-- Exaluating plan₁ on the initial state P given the simple ActionHandler.
world-eval : World
world-eval =  from-just (⟦ plan₁ ⟧ (canonical-σ Γ₁) (stateToWorld P))

{- Output of world-eval
isIn taxi3 location3 ∷
isIn person1 location3 ∷
isIn person3 location1 ∷
isIn taxi1 location2 ∷
isIn taxi2 location2 ∷ isIn person2 location2 ∷ []
-}

---------------------------------------------------------------------------------------

-- Evaluating plan₁ on the initial state P given ActionHandler₂ where we update the function ourselver.
world-eval-function : World
world-eval-function = from-just (⟦ plan₁ ⟧₂ (canonical-σ₂ Γ₁) numberOfTrips (stateToWorld P))

-- Both of evaluations return the same world 
testEqual : world-eval ≡ world-eval-function
testEqual = refl

----------------------------------------------------------------------------------------

--Also works with handler where driving is agnostic to trips.
world-eval-function-ag : World
world-eval-function-ag = from-just (⟦ plan₁ ⟧₃ (canonical-σ₃ Γ₁) numberOfTrips (stateToWorld P))

-- Both of evaluations return the same world 
testEqual2 : world-eval ≡ world-eval-function-ag
testEqual2 = refl

----------------------------------------------------------------------------------------
-- Here is an example where the function should fail

numberOfTripsFail : C taxi -> Nat
numberOfTripsFail taxi1 = 2
numberOfTripsFail taxi2 = 2
numberOfTripsFail taxi3 = 2

open import Data.Bool

world-eval-function-fail : Maybe World  
world-eval-function-fail = (⟦ plan₁ ⟧₂ (canonical-σ₂ Γ₁) numberOfTripsFail (stateToWorld P))

world-eval-function-fail-proof : (⟦ plan₁ ⟧₂ (canonical-σ₂ Γ₁) numberOfTripsFail (stateToWorld P)) ≡ nothing
world-eval-function-fail-proof = refl 

