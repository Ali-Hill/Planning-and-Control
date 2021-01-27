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

module Handlers.Taxi_Typed   {numberOfTrips : C taxi -> Nat}
                             {maxTrips : C taxi -> Nat}  where
  

-- This imports our typed planning Grammar

open import Grammar_Types {Action} {R} {Type} {C} renaming (NPred to State) hiding (¬_)


----------------------------------------------------------------------------------------

open import Data.Nat hiding (_≟_)
open import Relation.Nullary
open import Data.Maybe


-- This is the type of an ActionHandler. An ActionHandler takes in an Action and a World and returns a new World.
-- This Action handler also has a type that ensures that every Action is associated with a taxi and that the taxi
-- will not exceed its max number of trips. Here we assume that the numberOfTrips function is an auto-updating oracle.

ActionHandler : Set
ActionHandler = Action -> {txi : C taxi} -> {suc (numberOfTrips txi) ≤ maxTrips txi} -> World -> World

open IsDecEquivalence isDecidable renaming (_≟_ to _≟ᵣ_)


-- Remove a predicate R from a world.
remove : R → World → World
remove x [] = []
remove x (y ∷ w) with x ≟ᵣ y
remove x (y ∷ w) | yes p = remove x w
remove x (y ∷ w) | no ¬p = y ∷ remove x w

-- World constructor from state
σα : State → World → World
σα [] w = w
σα ((+ , x) ∷ N) w = x ∷ σα N w
σα ((- , x) ∷ N) w = remove x (σα N w)

-- Canonical Handler
canonical-σ : Γ → ActionHandler
canonical-σ Γ α = σα (proj₂ (Γ α))

-- Evaluation function. This evaluates an entire plan and produces a world if the type requirements of the
-- ActionHandler can be met. 
⟦_⟧ : Plan → ActionHandler → World → Maybe World
⟦ doAct (drivePassenger txi x₁ x₂ x₃) f ⟧ σ w with suc (numberOfTrips txi) ≤?  maxTrips txi
... | no ¬p = nothing
... | yes p = ⟦ f ⟧ σ (σ ((drivePassenger txi x₁ x₂ x₃)) {txi} {p} w)
⟦ doAct (drive txi x₁ x₂) f ⟧ σ w  with suc (numberOfTrips txi) ≤?  maxTrips txi
... | no ¬p = nothing
... | yes p = ⟦ f ⟧ σ (σ (drive txi x₁ x₂) {txi} {p} w)
⟦ halt ⟧ σ w = just w
--------------------------------------------------------------------------------------------------------------

-- Allowing for the update of functions

open IsDecEquivalence (isDEC taxi) 


-- This ActionHandler also  ensures that every Action is associated with a taxi and that the taxi will not exceed
-- its max number of trips however in this case we supply the function to the ActionHandler so it can be updated.
ActionHandler2 : Set
ActionHandler2 = Action
                -> {txi : C taxi}
                -> {noOfTrips : C taxi -> Nat}
                -> {suc (noOfTrips txi) ≤ maxTrips txi}
                -> World -> World

-- Canonical Handler
canonical-σ₂ : Γ → ActionHandler2
canonical-σ₂ Γ α = σα (proj₂ (Γ α))

open import Agda.Builtin.Reflection

--This function allows us to update a single mapping from (C taxi -> Nat) in function mapping (C taxi -> Nat).
updateFunction : C taxi -> Nat -> (C taxi -> Nat) -> (C taxi -> Nat)
updateFunction txi n noOfTrips t with (t ≟ txi)
... | no ¬p = noOfTrips t
... | yes p = n

-- Evaluation function. This evaluates an entire plan and produces a world if the type requirements of the
-- ActionHandler can be met. 
⟦_⟧₂ : Plan -> ActionHandler2
            -> (noOfTrips : C taxi -> Nat)
            -> World
            -> Maybe World
⟦ doAct (drivePassenger txi p1 l1 l2) f ⟧₂ σ noOfTrips w with suc (noOfTrips txi) ≤?  maxTrips txi
... | no ¬p = nothing
... | yes p = ⟦ f ⟧₂ σ
                     (updateFunction txi ((suc (noOfTrips txi))) noOfTrips)
                     (σ ((drivePassenger txi p1 l1 l2)) {txi} {noOfTrips} {p} w)
⟦ doAct (drive txi l1 l2) f ⟧₂ σ noOfTrips w with suc (noOfTrips txi) ≤?  maxTrips txi
... | no ¬p = nothing
... | yes p = ⟦ f ⟧₂ σ
                     (updateFunction txi ((suc (noOfTrips txi))) noOfTrips)
                     (σ ((drive txi l1 l2)) {txi} {noOfTrips} {p} w)
⟦ halt ⟧₂ σ noOfTrips w = just w


--------------------------------------------------------------------------------------------------------------

open import Data.Empty
open import Data.Unit hiding (_≤_ ; _≤?_)
open import Data.Sum

-- This example assumes that drive does not affect the number of trips so has to be modified

-- True if the action does not affect the number of trips taken
TripAgnostic : Action -> Set
TripAgnostic (drivePassenger x x₁ x₂ x₃) = ⊥
TripAgnostic (drive x x₁ x₂) = ⊤

--Here we assume that even if we have reached the max trips we can still do other actions that do not effect trips.
-- Here we modify handler2 to only require the proof (suc (noOfTrips txi) ≤ maxTrips) if we are using an action that effects
-- the number of trips.
ActionHandler3 : Set
ActionHandler3 = (α : Action) 
                -> {txi : C taxi}
                -> {noOfTrips : C taxi -> Nat}
                -> {suc (noOfTrips txi) ≤ maxTrips txi ⊎ TripAgnostic α} 
                -> World -> World


⟦_⟧₃ : Plan -> ActionHandler3
            -> (noOfTrips : C taxi -> Nat)
            -> World
            -> Maybe World
⟦ doAct (drivePassenger txi p1 l1 l2) f ⟧₃ σ noOfTrips w with suc (noOfTrips txi) ≤?  maxTrips txi
... | no ¬p = nothing
... | yes p = ⟦ f ⟧₃ σ
                     (updateFunction txi ((suc (noOfTrips txi))) noOfTrips)
                     (σ ((drivePassenger txi p1 l1 l2)) {txi} {noOfTrips} {inj₁ p} w)
⟦ doAct (drive txi l1 l2) f ⟧₃ σ noOfTrips w = ⟦ f ⟧₃ σ
                                                 noOfTrips
                                                 (σ ((drive txi l1 l2)) {txi} {noOfTrips} {inj₂ tt} w)
⟦ halt ⟧₃ σ noOfTrips w = just w

-- Canonical Handler
canonical-σ₃ : Γ → ActionHandler3
canonical-σ₃ Γ α = σα (proj₂ (Γ α))
