module Logic where

open import Level
open import Data.Product
open import Data.Sum

---
--- Propositional logic
---

_and_ : (A : Set) (B : Set) → Set
infixr 2 _and_
A and B = A × B

_or_ : (A : Set) (B : Set) → Set
infixr 1 _or_
A or B = A ⊎ B

---
--- Π-Types
---

-- Π : ∀ {a b} (A : Set a) → (P : A → Set b) → Set (a ⊔ b)
-- Π A P = (x : A) → P x

-- infix 1 Π-syntax

-- Π-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
-- Π-syntax = Π

-- syntax Π-syntax A (λ x → B) = Π[ x ∈ A ] B
