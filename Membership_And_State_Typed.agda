open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level

module Membership_And_State_Typed  {Action : Set} {R : Set}  {Type : Set} {C : Type -> Set}
                                            {isDE : IsDecEquivalence {A = R} (_≡_) }  where

open import Grammar_Types {Action} {R} {Type} {C}

open import Data.Product
open import Relation.Nullary
open import Data.Empty
open import Data.Unit hiding (_≟_)
open IsDecEquivalence isDE hiding (refl)
open import AnyLemma
open import Data.List hiding (any)


-- New Definitions Of Membership -----------------------------------------------------------------

--Defining above using Any instead
_atom≡_ : (a : R) (p : PredMap) -> Set
a atom≡ s = a ≡ proj₂ s

_∈S_ : (a : R) (s : NPred) -> Set
a ∈S s = Any (a atom≡_) s
  
-- Is an atom not in a State
_∉S_ : (a : R) (s : NPred) -> Set
a ∉S s = Relation.Nullary.¬ (a ∈S s)

isInState  : (a : R) -> (s : NPred) -> Dec (a ∈S s)
isInState a s = any? (λ x → a ≟ proj₂ x) s
-- uses any in Data.List.Relation.Unary.Any renamed to any? in new version of std lib

------------------------------------------------------------------------------------------------

-- A State is valid if there is no duplicate predicates in the State.
validState : NPred -> Set
validState [] = ⊤
validState ((t , At') ∷ s) with isInState At' s
validState ((t , At') ∷ s) | yes p = ⊥
validState ((t , At') ∷ s) | no ¬p = validState s

--Decidability of State validity
decValidState : (s : NPred) -> Dec (validState s)
decValidState [] = yes tt
decValidState ((t , At') ∷ s) with isInState At' s
decValidState ((t , At') ∷ s) | yes p =  no λ ()
decValidState ((t , At') ∷ s) | no ¬p = decValidState s


open Data.Product renaming (_,_ to _↝_)
open import Relation.Nullary

-- Decidablity of polarities
decZ : (z : Polarity) -> (z' : Polarity) -> Dec (z ≡ z')
decZ + + = yes refl
decZ + - = no (λ ())
decZ - + = no (λ ())
decZ - - = yes refl

-- Decidablity of PredMaps
isSame : (s : PredMap) -> (s' : PredMap) -> Dec (s ≡ s')
isSame (z , a) (z' , a') with decZ z z' | a ≟ a'
isSame (z ↝ a) (.z ↝ .a) | yes refl | yes refl = yes refl
isSame (z ↝ a) (.z ↝ a') | yes refl | no ¬p = no λ { refl → ¬p refl}
isSame (z ↝ a) (z' ↝ a') | no ¬p | yes p = no λ { refl → ¬p refl}
isSame (z ↝ a) (z' ↝ a') | no ¬p | no ¬p₁ = no λ { refl → ¬p refl}

{-
--union defined using minus operator
_⊔N_ : NPred →  NPred → NPred
P ⊔N [] = P
P ⊔N ((z , a) ∷ Q) with isInState a P
... | no ¬p = (z , a) ∷ P ⊔N Q
... | yes p = (z , a) ∷ (P AnyLemma.─ p) ⊔N Q

-}

open import Data.List.Membership.Propositional

del : R → NPred → NPred
del x [] = []
del x ((t' , x') ∷ M) with x ≟ x'
del x ((t' , x') ∷ M) | yes p =  del x M
del x ((t' , x') ∷ M) | no ¬p = (t' , x') ∷ del x M

del-spec : ∀ t x N → (t , x) ∉ del x N
del-spec t x [] ()
del-spec t x ((t' , y) ∷ N) tx∈N' with x ≟ y
del-spec t x ((t' , y) ∷ N) tx∈N' | yes p = del-spec t x N tx∈N'
del-spec .t' .y ((t' , y) ∷ N) (here refl) | no ¬p = ¬p _≡_.refl
del-spec t x ((t' , y) ∷ N) (there tx∈N') | no ¬p =  del-spec t x N tx∈N'


del-∈ : ∀{M y x} → x ∈ del y M → x ∈ M
del-∈ {[]}             ()
del-∈ {(t , z) ∷ M}{y} x∈ with y ≟ z
del-∈ {(t , z) ∷ M} {y} x∈ | yes p = there (del-∈ x∈)
del-∈ {(t , z) ∷ M} {y} (here refl) | no ¬p = here _≡_.refl
del-∈ {(t , z) ∷ M} {y} (there x∈) | no ¬p = there (del-∈ x∈)


-- Override operator
_⊔N_ : NPred → NPred → NPred
M ⊔N [] = M
M ⊔N ((t , x) ∷ N) = (t , x) ∷ del x M ⊔N N
