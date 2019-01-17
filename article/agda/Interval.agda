module Interval where

open import Agda.Primitive
open import Data.Product

open import Program
open import Order

data Interval {P : Prog} {p : Pos P} {q : Pos P} (l : p ≤ q) : (P : Prog) → Set where
  CC : (p ≤ q) → Interval P
  -- OC : {P : Prog} → Pos P → Pos P → Interval P
  -- CO : {P : Prog} → Pos P → Pos P → Interval P
  -- OO : {P : Prog} → Pos P → Pos P → Interval P

-- area : ∀ {ℓ} (P : Prog) → Set (lsuc ℓ)
-- area {ℓ} P = Σ[ I ∈ Set ℓ ] (Interval P)

-- ∨ : {P : Prog} → area P → area P → area P
-- ∨ (I , A) (J , B) = {!!}
