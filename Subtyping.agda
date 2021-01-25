open import Data.List hiding (any)
open import Data.Product
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any
open import Relation.Nullary
open import Relation.Binary

module Subtyping {A : Set} {decA : (x : A) -> (y : A) -> Dec (x ≡ y) } where

State = List A

-- Subtyping
infix 3 _<:_
data _<:_ : State → State → Set where
  []<:_ : ∀ Q → [] <: Q
  atom<: : ∀{x P Q} → x ∈ Q → P <: Q → x ∷ P <: Q

-- Extension of subtyping
<:atom : (P : State) -> (Q : State) -> (s : A) -> P <: Q -> P <: s ∷ Q
<:atom .[] Q s ([]<: .Q) = []<: (s ∷ Q)
<:atom (p ∷ P) Q s (atom<: x₂ x₁) = atom<: (there x₂) (<:atom P Q s x₁)

-- Reflexivity of subtyping
reflSub : (S : State) -> S <: S
reflSub [] = []<: []
reflSub (s ∷ S) = atom<: (here refl) (<:atom S S s (reflSub S))

helpTrans : ∀ x -> (P : State) -> (Q : State ) -> x ∈ P -> P <: Q -> x ∈ Q
helpTrans ._ .(_ ∷ _) Q (here refl) (atom<: x x₂) = x
helpTrans x .(_ ∷ _) Q (there x₁) (atom<: x₂ x₃) = helpTrans x _ Q x₁ x₃

-- Transitivity of subtyping
transSub : (L : State) -> (M : State) -> (N : State) -> L <: M -> M <: N -> L <: N
transSub [] M N x x₁ = []<: N
transSub (._ ∷ L) M N (atom<: x x₂) x₁ = atom<: (helpTrans _ M N x x₁) (transSub L M N x₂ x₁)

-- Weakening of subtyping
weakSub : (s : A) -> (P : State) -> (Q : State) ->  (s ∷ P) <: Q -> P <: Q
weakSub ._ P Q (atom<: x₁ x₂) = x₂ 

isSameInState : (s : A) -> (S : State) -> Dec (s ∈ S)
isSameInState s S = any? (λ x → decA s x) S

decSub : (P : State) -> (Q : State) -> Dec (P <: Q)
decSub [] Q = yes ([]<: Q)
decSub (p ∷ P) Q with isSameInState p Q
decSub (p ∷ P) Q | no ¬p = no (λ { (atom<: x₁ x) → ¬p x₁})
decSub (p ∷ P) Q | yes p₁ with decSub P Q
decSub (p ∷ P) Q | yes p₁ | no ¬p = no (λ { (atom<: x₁ x) → ¬p x})
decSub (p ∷ P) Q | yes p₁ | yes p₂ = yes (atom<: p₁ p₂)

