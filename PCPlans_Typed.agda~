-- Alasdair Hill
-- This file defines Planning languages as types, plans as prrof terms approach to PDDL

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level

--------------------------------------------------------
--  Definition of formulae, possible world semantics, actions, plans

--
-- The following module declarartion allows to develop the file parametrised on an abstract set R of predicates
-- an an abstract set A of declared actions. The former must have decidable equivalence.



module PCPlans_Typed {Action : Set} {R : Set} {Type : Set} {C : Type -> Set} {isDE : IsDecEquivalence {A = R} (_≡_) }
                                              {isDEC : (t : Type) -> IsDecEquivalence {A = C t} (_≡_) }
                                              {isDECA : IsDecEquivalence {A = Action} (_≡_) } where

-- R is a predicate

open import Agda.Builtin.Nat hiding (_*_ ; _+_ ; _-_; zero)
open import Data.Vec hiding (_++_; remove)
open import Data.List hiding (any)
open import Data.Product

open import Grammar_Types {Action} {R} {Type} {C}

open import Membership_And_State_Typed {Action} {R} {Type} {C} {isDE} 
open import Subtyping {PredMap} {isSame} hiding (State)

---------------------------------------------------------------
-- Figure 10: well-typing relation
--
data _⊢_∶_↝_ : Γ → Plan → NPred → NPred → Set where
  halt : ∀{Γ M' M} → M' <: M → Γ ⊢ halt ∶ M ↝ M'
  seq : ∀{α M₁ M₃ Γ f}
      → proj₁ (Γ α) <: M₁
      -- -> validS (M₁ ⊔N proj₂ (Γ α))
      → Γ ⊢ f ∶ M₁ ⊔N proj₂ (Γ α) ↝ M₃
      → Γ ⊢ doAct α f ∶ M₁ ↝ M₃
      
---------------------------------------------------------------

open import Data.Maybe
open import Relation.Nullary

--We could create an error data type for errors
solver : (Γ₁ : Γ) -> (f : Plan) -> (P : NPred) -> (Q : NPred) ->  Maybe (Γ₁ ⊢ f ∶ P ↝ Q)
solver Γ₁ (doAct x f) P Q with decSub (proj₁ (Γ₁ x)) P
... | no ¬p = nothing
... | yes p with solver Γ₁ f (P ⊔N (proj₂ (Γ₁ x))) Q
... | nothing = nothing
... | just x₁ = just (seq p x₁)
solver Γ₁ halt P Q with decSub Q P
... | no ¬p = nothing
... | yes p = just (halt p)

{- open import Data.String hiding (_≟_)

solver2 : (Γ₁ : Γ) -> (f : Plan) -> (P : NPred) -> (Q : NPred) -> (Γ₁ ⊢ f ∶ P ↝ Q) ⊎ (Action ⊎ String)
solver2 Γ₁ (doAct x f) P Q with decSub (proj₁ (Γ₁ x)) P
... | no ¬p = inj₂ (inj₁ x)
... | yes p with solver2 Γ₁ f (P ⊔N (proj₂ (Γ₁ x))) Q
... | inj₁ x₁ = inj₁ (seq p x₁)
... | inj₂ (inj₁ x₁) = inj₂ (inj₁ x₁)
... | inj₂ (inj₂ y) = inj₂ (inj₂ y) --this case should be impossible
solver2 Γ₁ halt P Q with decSub Q P
... | no ¬p = inj₂ (inj₂ "Subtype Halt Issue") --giving an action here does not make sense and is impossible. Need to create some sort of error datatype.
... | yes p = inj₁ (halt p)

-}
