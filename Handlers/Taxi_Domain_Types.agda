module Handlers.Taxi_Domain_Types where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open import Data.List
open import Data.List.Relation.Unary.Any
open import Relation.Nullary using (yes; no; Dec)
open import Level
open import Tactic.Deriving.Eq

-- Types for out domain.
data Type : Set where
  taxi : Type
  location : Type
  person : Type
-- EqT : Eq T
unquoteDecl EqT = deriveEq EqT (quote Type)

-- A list of typed constants. 
data C : Type -> Set where
  taxi1 taxi2 taxi3 : C taxi 
  person1 person2 person3 : C person
  location1 location2 location3 : C location
-- EqC : Eq C
unquoteDecl EqC = deriveEq EqC (quote C)

-- Predicates 
data R : Set where
  isIn : ∀ {t} -> C t → C location → R
-- EqR : Eq R
unquoteDecl EqR = deriveEq EqR (quote R)

-- Actions
data Action : Set where
  drivePassenger : C taxi → C person → C location → C location → Action
  drive : C taxi → C location → C location → Action
-- EqAction : Eq Action
unquoteDecl EqAction = deriveEq EqAction (quote Action)

-----------------------------------------------------------------------------------
-- The rest is proving decidable equality for all of the above data types.

open import Mangle using (mangle)

isDECT : IsDecEquivalence {zero} {zero} (_≡_ {A = Type})
isDECT = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = mangle  }

isDEC : (t : Type) -> IsDecEquivalence {zero} {zero} (_≡_ {A = C t})
isDEC t = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = mangle  }

open IsDecEquivalence isDECT hiding (refl ; sym ; trans) renaming (_≟_ to _≟ₜ_)
open import Relation.Nullary

decSingleC : (t : Type) -> (x y : C t) -> Dec (x ≡ y)
decSingleC t x y = x ≟c y
  where open IsDecEquivalence (isDEC t) renaming (_≟_ to _≟c_)

isDecidable : IsDecEquivalence {zero} {zero} (_≡_ {A = R})
isDecidable = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
 _≟_ = mangle  }

isDECA : IsDecEquivalence {zero} {zero} (_≡_ {A = Action})
isDECA = record { isEquivalence = record {
  refl = λ {x} → refl ;
  sym = λ x → sym x ;
  trans = trans } ;
  _≟_ = mangle  }


