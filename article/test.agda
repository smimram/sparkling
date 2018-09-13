open import Relation.Binary.PropositionalEquality
open import Data.Bool

-- absurd : {A : Set} → (false ≡ true) → A
-- absurd = λ ()

-- absurd : {A : Set} → (false ≡ true) → A
-- absurd p = (λ ()) p

-- absurd : {A : Set} → ((b : Bool) → b ≡ true) → A
-- absurd f = (λ ()) (f false)

absurd : {A : Set} → ((b : Bool) → b ≡ true) → A
absurd f = g (f false)
  where
  g : {A : Set} → (false ≡ true) → A
  g ()
