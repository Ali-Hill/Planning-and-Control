module Grammar_Types  {Action : Set} {R : Set} {Type : Set} {C : Type -> Set} where

-- R is a predicate

data Form : Set where
  _∧_ : Form → Form → Form
  ¬_ : R  → Form
  atom : R → Form
infixl 4 _∧_
infixl 5 ¬_

--------------------------------------------------------
-- Figure 4. Possible worlds 
--

open import Data.List

World : Set
World = List R

data Polarity : Set where
  + - : Polarity

neg : Polarity → Polarity
neg + = -
neg - = +

--------------------------------------------------------
-- Figure 6. Declarative (possible world) semantics
-- 

open import Data.List.Membership.Propositional
--open import Data.List.Any.Membership.Propositional 


-- Entailment Relation
infix 3 _⊨[_]_
data _⊨[_]_ : World → Polarity → Form → Set where
  flip : ∀{w t A} → w ⊨[ neg t ] (atom A) → w ⊨[ t ] ¬ A
  both : ∀{w t P Q} → w ⊨[ t ] P → w ⊨[ t ] Q → w ⊨[ t ] P ∧ Q
  somewhere : ∀{w a} → a ∈ w → w ⊨[ + ] atom a
  nowhere : ∀{w a} → a ∉ w → w ⊨[ - ] atom a

open import Data.Product

-- A pair containing a predicate and polarity
PredMap : Set
PredMap = (Polarity × R)

-- A list containing pairs of polarities and predicates
NPred : Set
NPred = List PredMap

-- Operational Semantics: normalisation function
infixr 3 _↓[_]_
_↓[_]_ : Form → Polarity → NPred → NPred
P ∧ Q ↓[ t ] N = Q ↓[ t ] P ↓[ t ] N
¬ x ↓[ t ] N = (neg t , x) ∷ N
atom x ↓[ t ] N = (t , x) ∷ N

---------------------------------------------------------------
-- Figure 7: Plans
--

data Plan : Set where
  doAct : Action → Plan → Plan
  halt : Plan

---------------------------------------------------------------
-- Figure 8
-- 

-- Context
Γ : Set
Γ = Action → NPred × NPred

--------------------------------------------------------

-- Relation between NPred and World
_∈⟨_⟩ : World → NPred → Set
w ∈⟨ N ⟩ = (∀ a → (+ , a) ∈ N → a ∈ w) × (∀ a → (- , a) ∈ N → a ∉ w)

--------------------------------------------------------
