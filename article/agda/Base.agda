open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Product
open import Data.Nat.Base renaming (_≤_ to _≤ℕ_) renaming (compare to ℕ-compare)

---
--- Equality
---

≡-comm : {A : Set} {a b : A} → (a ≡ b) → (b ≡ a)
≡-comm refl = refl

≡-× : {A B : Set} {a a' : A} {b b' : B} → (a ≡ a') → (b ≡ b') → (a , b) ≡ (a' , b')
≡-× refl refl = refl

---
--- Natural numbers
---

≤ℕ-suc : {n n' : ℕ} → (n ≤ℕ n') → (suc n ≤ℕ suc n')
≤ℕ-suc {zero} {n'} l = s≤s l
≤ℕ-suc {suc n} {zero} l = s≤s l
≤ℕ-suc {suc n} {suc n'} l = s≤s l

suc-acyclic : {n : ℕ} → (suc n ≤ℕ n) → ⊥
suc-acyclic (s≤s l) = suc-acyclic l
